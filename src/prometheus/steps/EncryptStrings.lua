local Step = require("prometheus.step")
local Ast = require("prometheus.ast")
local Scope = require("prometheus.scope")
local RandomStrings = require("prometheus.randomStrings")
local Parser = require("prometheus.parser")
local Enums = require("prometheus.enums")
local logger = require("logger")
local visitast = require("prometheus.visitast")
local util     = require("prometheus.util")
local AstKind = Ast.AstKind

local EncryptStrings = Step:extend()
EncryptStrings.Description = "This Step will encrypt strings within your Program."
EncryptStrings.Name = "Encrypt Strings"

EncryptStrings.SettingsDescriptor = {}

function EncryptStrings:init(settings) end

function EncryptStrings:CreateEncrypionService()
    local usedSeeds = {}

    local secret_key_6 = math.random(0, 63)
    local secret_key_7 = math.random(0, 127)
    local secret_key_44 = math.random(0, 17592186044415)
    local secret_key_8 = math.random(0, 255)
    local offset_key = math.random(1, 50)

    local floor = math.floor

    -- Select a random reverse implementation out of ten custom ones.
    local reverse_impl = math.random(1, 10)
    -- Select a random encryption method out of three custom ones (bit32-based methods removed)
    local encrypt_impl = math.random(1, 3)

    local function primitive_root_257(idx)
        local g, m, d = 1, 128, 2 * idx + 1
        repeat
            g, m, d = g * g * (d >= m and 3 or 1) % 257, m / 2, d % m
        until m < 1
        return g
    end

    local param_mul_8 = primitive_root_257(secret_key_7)
    local param_mul_45 = secret_key_6 * 4 + 1
    local param_add_45 = secret_key_44 * 2 + 1

    local state_45 = 0
    local state_8 = 2

    local prev_values = {}
    local function set_seed(seed_53)
        state_45 = seed_53 % 35184372088832
        state_8 = seed_53 % 255 + 2
        prev_values = {}
    end

    local function gen_seed()
        local seed
        repeat
            seed = math.random(0, 35184372088832)
        until not usedSeeds[seed]
        usedSeeds[seed] = true
        return seed
    end

    local function get_random_32()
        state_45 = (state_45 * param_mul_45 + param_add_45) % 35184372088832
        repeat
            state_8 = state_8 * param_mul_8 % 257
        until state_8 ~= 1
        local r = state_8 % 32
        local n = floor(state_45 / 2 ^ (13 - (state_8 - r) / 32)) % 2 ^ 32 / 2 ^ r
        return floor(n % 1 * 2 ^ 32) + floor(n)
    end

    local function get_next_pseudo_random_byte()
        if #prev_values == 0 then
            local rnd = get_random_32()
            local low_16 = rnd % 65536
            local high_16 = (rnd - low_16) / 65536
            local b1 = low_16 % 256
            local b2 = (low_16 - b1) / 256
            local b3 = high_16 % 256
            local b4 = (high_16 - b3) / 256
            prev_values = { b1, b2, b3, b4 }
        end
        return table.remove(prev_values)
    end

    -- Ten custom reverse string implementations

    local function string_reverse1(str)
        local len = string.len(str)
        local result = {}
        for i = len, 1, -1 do
            result[len - i + 1] = string.sub(str, i, i)
        end
        return table.concat(result)
    end

    local function string_reverse2(str)
        local len = string.len(str)
        local result = {}
        for i = 1, len do
            result[i] = string.char(string.byte(str, len - i + 1))
        end
        return table.concat(result)
    end

    local function string_reverse3(str)
        local result = {}
        local len = string.len(str)
        for i = 1, len do
            table.insert(result, 1, string.sub(str, i, i))
        end
        return table.concat(result)
    end

    local function string_reverse4(str)
        local result = ""
        for i = string.len(str), 1, -1 do
            result = result .. string.sub(str, i, i)
        end
        return result
    end

    local function string_reverse5(str)
        local chars = {}
        for c in str:gmatch(".") do
            table.insert(chars, c)
        end
        local function rev(i, j)
            if i >= j then return end
            chars[i], chars[j] = chars[j], chars[i]
            rev(i + 1, j - 1)
        end
        rev(1, #chars)
        return table.concat(chars)
    end

    local function string_reverse6(str)
        local result = {}
        local idx = 1
        string.gsub(str, ".", function(c)
            result[string.len(str) - idx + 1] = c
            idx = idx + 1
        end)
        return table.concat(result)
    end

    local function string_reverse7(str)
        if #str <= 1 then return str end
        return string_reverse7(string.sub(str, 2)) .. string.sub(str, 1, 1)
    end

    local function string_reverse8(str)
        local len = string.len(str)
        local half = math.floor(len / 2)
        local chars = {}
        for i = 1, len do
            chars[i] = string.sub(str, i, i)
        end
        for i = 1, half do
            chars[i], chars[len - i + 1] = chars[len - i + 1], chars[i]
        end
        return table.concat(chars)
    end

    local function string_reverse9(str)
        -- Chunk-based reversal (chunks of 3)
        local result = ""
        local len = string.len(str)
        local chunkSize = 3
        for i = len, 1, -chunkSize do
            local chunk = ""
            for j = i, math.max(i - chunkSize + 1, 1), -1 do
                chunk = chunk .. string.sub(str, j, j)
            end
            result = result .. chunk
        end
        return result
    end

    local function string_reverse10(str)
        local bytes = {string.byte(str, 1, -1)}
        for i = 1, math.floor(#bytes / 2) do
            bytes[i], bytes[#bytes - i + 1] = bytes[#bytes - i + 1], bytes[i]
        end
        return string.char(unpack(bytes))
    end

    local reverse_funcs = { 
        string_reverse1, string_reverse2, string_reverse3, 
        string_reverse4, string_reverse5, string_reverse6,
        string_reverse7, string_reverse8, string_reverse9,
        string_reverse10
    }
    local string_reverse = reverse_funcs[reverse_impl]

    -- Three different encryption methods (methods using bit32 removed)

    local function encrypt1(str)
        -- Original deduction method
        local seed = gen_seed()
        set_seed(seed)
        local len = string.len(str)
        local out = {}
        local prevVal = secret_key_8
        for i = 1, len do
            local byte = string.byte(str, i)
            out[i] = string.char((byte - (get_next_pseudo_random_byte() + prevVal)) % 256)
            prevVal = byte
        end
        local encrypted = table.concat(out)
        return string_reverse(encrypted), seed
    end

    local function encrypt2(str)
        -- Original addition method
        local seed = gen_seed()
        set_seed(seed)
        local len = string.len(str)
        local out = {}
        local prevVal = secret_key_8
        for i = 1, len do
            local byte = string.byte(str, i)
            local randomByte = get_next_pseudo_random_byte()
            local encrypted_byte = (byte + randomByte + prevVal + offset_key) % 256
            out[i] = string.char(encrypted_byte)
            prevVal = byte
        end
        local encrypted = table.concat(out)
        return string_reverse(encrypted), seed
    end

    local function encrypt5(str)
        -- Substitution with dynamic offset
        local seed = gen_seed()
        set_seed(seed)
        local len = string.len(str)
        local out = {}
        local prevVal = secret_key_8
        local key_sum = 0
        for i = 1, len do
            local byte = string.byte(str, i)
            local randomByte = get_next_pseudo_random_byte()
            key_sum = (key_sum + randomByte) % 256
            local encrypted_byte = (byte + key_sum + prevVal) % 256
            out[i] = string.char(encrypted_byte)
            prevVal = byte
        end
        local encrypted = table.concat(out)
        return string_reverse(encrypted), seed
    end

    local encrypt_funcs = {encrypt1, encrypt2, encrypt5}
    local encrypt = encrypt_funcs[encrypt_impl]

    local function genCode()
        local string_reverse_impls = {
            [[
    local function string_reverse(str)
        local length = len(str)
        local result = table.create(length)
        for i = length, 1, -1 do
            result[length - i + 1] = sub(str, i, i)
        end
        return table.concat(result)
    end]],
            [[
    local function string_reverse(str)
        local length = len(str)
        local result = table.create(length)
        for i = 1, length do
            result[i] = char(byte(str, length - i + 1))
        end
        return table.concat(result)
    end]],
            [[
    local function string_reverse(str)
        local result = {}
        for i = 1, len(str) do
            table.insert(result, 1, sub(str, i, i))
        end
        return table.concat(result)
    end]],
            [[
    local function string_reverse(str)
        local result = ""
        for i = len(str), 1, -1 do
            result = result .. sub(str, i, i)
        end
        return result
    end]],
            [[
    local function string_reverse(str)
        local chars = {}
        for c in str:gmatch(".") do
            table.insert(chars, c)
        end
        local function rev(i, j)
            if i >= j then return end
            chars[i], chars[j] = chars[j], chars[i]
            rev(i + 1, j - 1)
        end
        rev(1, #chars)
        return table.concat(chars)
    end]],
            [[
    local function string_reverse(str)
        local result = {}
        local idx = 1
        string.gsub(str, ".", function(c)
            result[len(str) - idx + 1] = c
            idx = idx + 1
        end)
        return table.concat(result)
    end]],
            [[
    local function string_reverse(str)
        if len(str) <= 1 then return str end
        return string_reverse(sub(str, 2)) .. sub(str, 1, 1)
    end]],
            [[
    local function string_reverse(str)
        local length = len(str)
        local half = floor(length / 2)
        local chars = {}
        for i = 1, length do
            chars[i] = sub(str, i, i)
        end
        for i = 1, half do
            chars[i], chars[length - i + 1] = chars[length - i + 1], chars[i]
        end
        return table.concat(chars)
    end]],
            [[
    local function string_reverse(str)
        -- Chunk-based reversal (chunks of 3)
        local result = ""
        local length = len(str)
        local chunkSize = 3
        for i = length, 1, -chunkSize do
            local chunk = ""
            for j = i, max(i - chunkSize + 1, 1), -1 do
                chunk = chunk .. sub(str, j, j)
            end
            result = result .. chunk
        end
        return result
    end]],
            [[
    local function string_reverse(str)
        local bytes = {byte(str, 1, -1)}
        for i = 1, floor(#bytes / 2) do
            bytes[i], bytes[#bytes - i + 1] = bytes[#bytes - i + 1], bytes[i]
        end
        return char(unpack(bytes))
    end]]
        }

        local decryption_impls = {
            -- Decrypt for encryption method 1 (deduction)
            [[
			for i=1, length do
				prevVal = (byte(str, i) + get_next_pseudo_random_byte() + prevVal) % 256
				realStringsLocal[seed] = realStringsLocal[seed] .. chars[prevVal + 1]
			end]],
            
            -- Decrypt for encryption method 2 (addition)
            [[
			for i=1, length do
				local randomByte = get_next_pseudo_random_byte()
				local encrypted_byte = byte(str, i)
				local decrypted_byte = (encrypted_byte - randomByte - prevVal - ]] .. tostring(offset_key) .. [[) % 256
				realStringsLocal[seed] = realStringsLocal[seed] .. chars[decrypted_byte + 1]
				prevVal = decrypted_byte
			end]],
            
            -- Decrypt for encryption method 5 (dynamic substitution)
            [[
			local key_sum = 0
			for i=1, length do
				local randomByte = get_next_pseudo_random_byte()
				key_sum = (key_sum + randomByte) % 256
				local encrypted_byte = byte(str, i)
				local decrypted_byte = (encrypted_byte - key_sum - prevVal) % 256
				realStringsLocal[seed] = realStringsLocal[seed] .. chars[decrypted_byte + 1]
				prevVal = decrypted_byte
			end]]
        }
        
        local selected_reverse_impl = string_reverse_impls[reverse_impl] or string_reverse_impls[1]
        local selected_decrypt_impl = decryption_impls[encrypt_impl]
		
		local code = [[
do
	local floor = math.floor
	local random = math.random
	local remove = table.remove
	local char = string.char
	local byte = string.byte
	local sub = string.sub
	local len = string.len
	local max = math.max
	local unpack = table.unpack
	local state_45 = 0
	local state_8 = 2
	local digits = table.create(0)
	local charmap = table.create(256)
	local i = 0

	local nums = table.create(256)
	for i = 1, 256 do
		nums[i] = i
	end

	repeat
		local idx = random(1, #nums)
		local n = remove(nums, idx)
		charmap[n] = char(n - 1)
	until #nums == 0

]] .. selected_reverse_impl .. [[

	local prev_values = table.create(0)
	local function get_next_pseudo_random_byte()
		if #prev_values == 0 then
			state_45 = (state_45 * ]] .. tostring(param_mul_45) .. [[ + ]] .. tostring(param_add_45) .. [[) % 35184372088832
			repeat
				state_8 = state_8 * ]] .. tostring(param_mul_8) .. [[ % 257
			until state_8 ~= 1
			local r = state_8 % 32
			local n = floor(state_45 / 2 ^ (13 - (state_8 - r) / 32)) % 2 ^ 32 / 2 ^ r
			local rnd = floor(n % 1 * 2 ^ 32) + floor(n)
			local low_16 = rnd % 65536
			local high_16 = (rnd - low_16) / 65536
			local b1 = low_16 % 256
			local b2 = (low_16 - b1) / 256
			local b3 = high_16 % 256
			local b4 = (high_16 - b3) / 256
			prev_values = table.create(4)
			prev_values[1] = b1
			prev_values[2] = b2
			prev_values[3] = b3
			prev_values[4] = b4
		end
		return table.remove(prev_values)
	end

	local realStrings = table.create(0)
	STRINGS = setmetatable(table.create(0), {
		__index = realStrings;
		__metatable = nil;
	})
  	function DECRYPT(str, seed)
		str = string_reverse(str)
		local realStringsLocal = realStrings
		if(realStringsLocal[seed]) then else
			prev_values = table.create(0)
			local chars = charmap
			state_45 = seed % 35184372088832
			state_8 = seed % 255 + 2
			local length = len(str)
			realStringsLocal[seed] = ""
			local prevVal = ]] .. tostring(secret_key_8) .. [[
			]] .. selected_decrypt_impl .. [[
		end
		return seed
	end
end]]
		return code
	end

	return {
		encrypt = encrypt,
		param_mul_45 = param_mul_45,
		param_mul_8 = param_mul_8,
		param_add_45 = param_add_45,
		secret_key_8 = secret_key_8,
		genCode = genCode,
        reverse_impl = reverse_impl,
        encrypt_impl = encrypt_impl
	}
end

function EncryptStrings:apply(ast, pipeline)
	local Encryptor = self:CreateEncrypionService()

	local code = Encryptor.genCode()
	local newAst = Parser:new({ LuaVersion = Enums.LuaVersion.Lua51 }):parse(code)
	local doStat = newAst.body.statements[1]

	local scope = ast.body.scope
	local decryptVar = scope:addVariable()
	local stringsVar = scope:addVariable()
	
	doStat.body.scope:setParent(ast.body.scope)

	visitast(newAst, nil, function(node, data)
		if(node.kind == AstKind.FunctionDeclaration) then
			if(node.scope:getVariableName(node.id) == "DECRYPT") then
				data.scope:removeReferenceToHigherScope(node.scope, node.id)
				data.scope:addReferenceToHigherScope(scope, decryptVar)
				node.scope = scope
				node.id    = decryptVar
			end
		end
		if(node.kind == AstKind.AssignmentVariable or node.kind == AstKind.VariableExpression) then
			if(node.scope:getVariableName(node.id) == "STRINGS") then
				data.scope:removeReferenceToHigherScope(node.scope, node.id)
				data.scope:addReferenceToHigherScope(scope, stringsVar)
				node.scope = scope
				node.id    = stringsVar
			end
		end
	end)

	visitast(ast, nil, function(node, data)
		if(node.kind == AstKind.StringExpression) then
			data.scope:addReferenceToHigherScope(scope, stringsVar)
			data.scope:addReferenceToHigherScope(scope, decryptVar)
			local encrypted, seed = Encryptor.encrypt(node.value)
			return Ast.IndexExpression(Ast.VariableExpression(scope, stringsVar), Ast.FunctionCallExpression(Ast.VariableExpression(scope, decryptVar), {
				Ast.StringExpression(encrypted), Ast.NumberExpression(seed),
			}))
		end
	end)

	table.insert(ast.body.statements, 1, doStat)
	table.insert(ast.body.statements, 1, Ast.LocalVariableDeclaration(scope, util.shuffle{ decryptVar, stringsVar }, {}))
	return ast
end

return EncryptStrings
