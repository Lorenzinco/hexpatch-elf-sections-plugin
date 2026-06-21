-- ELF section editor plugin for HexPatch.
--
-- The current HexPatch Lua Data API can overwrite bytes but cannot resize the
-- opened buffer. Adding/removing ELF sections usually changes the file length,
-- so this plugin builds a complete patched image and prompts for an output path
-- whenever the operation resizes the file. If the rewritten image happens to have
-- the same length, it is copied back into the open buffer.
--
-- Useful custom settings:
--   elf_section_name         default new section name, default ".hexpatch"
--   elf_section_size         default new section size, default 0x1000
--   elf_section_perms        default permissions: R/W/X/A combination, default "RW"
--   elf_section_align        default file alignment, default 0x10

local M = {}

local UI = {
	selected = 1,
	mode = "list",
	pending = nil,
	message = nil,
	sections = {},
	add_form = nil,
	save_path = "patched.elf",
}

local SHT_SYMTAB = 2
local SHT_RELA = 4
local SHT_NOBITS = 8
local SHT_REL = 9
local SHT_DYNSYM = 11
local SHF_WRITE = 0x1
local SHF_ALLOC = 0x2
local SHF_EXECINSTR = 0x4
local SHN_LORESERVE = 0xff00
local DEFAULT_NAME = ".hexpatch"
local DEFAULT_SIZE = "0x1000"
local DEFAULT_ALIGN = "0x10"
local BOLD = 1

local function clone_bytes(bytes)
	local out = {}
	for i = 1, #bytes do out[i] = bytes[i] end
	return out
end

local function bytes_from_context(context)
	local out = {}
	local len = context.data.len
	if type(len) == "function" then len = context.data:len() end
	for i = 0, len - 1 do out[#out + 1] = context.data:get(i) end
	return out
end

local function apply_bytes_to_context(context, bytes)
	local len = context.data.len
	if type(len) == "function" then len = context.data:len() end
	if len ~= #bytes then return false, "rewritten file length changed from " .. len .. " to " .. #bytes end
	for i = 1, #bytes do context.data:set(i - 1, bytes[i]) end
	return true
end

local function read_cstr(bytes, off0)
	local chars = {}
	local i = off0 + 1
	while i <= #bytes and bytes[i] ~= 0 do
		chars[#chars + 1] = string.char(bytes[i])
		i = i + 1
	end
	return table.concat(chars)
end

local function parse_integer(value, default)
	if type(value) == "number" then return value end
	local s = tostring(value or ""):match("^%s*(.-)%s*$")
	if s == "" then return default end
	local hex = s:match("^0[xX](%x+)$")
	if hex then return tonumber(hex, 16) or default end
	if s:match("^%d+$") then return tonumber(s, 10) or default end
	return default
end
M.parse_integer = parse_integer

local function align_up(v, a)
	a = math.max(parse_integer(a, 1) or 1, 1)
	return math.floor((v + a - 1) / a) * a
end

local function make_rw(bytes, endian)
	local function read_u(off0, size)
		local v = 0
		if endian == "little" then
			for i = size - 1, 0, -1 do v = v * 256 + bytes[off0 + i + 1] end
		else
			for i = 0, size - 1 do v = v * 256 + bytes[off0 + i + 1] end
		end
		return v
	end
	local function write_u(off0, size, value)
		value = math.floor(value or 0)
		if endian == "little" then
			for i = 0, size - 1 do
				bytes[off0 + i + 1] = value % 256
				value = math.floor(value / 256)
			end
		else
			for i = size - 1, 0, -1 do
				bytes[off0 + i + 1] = value % 256
				value = math.floor(value / 256)
			end
		end
	end
	return read_u, write_u
end

-- O(n) splice helpers. The previous table.insert/table.remove-per-byte approach
-- was O(n*m) and became visibly slow on larger binaries.
local function insert_bytes(bytes, off0, inserted)
	local m = #inserted
	if m == 0 then return end
	local n = #bytes
	for i = n, off0 + 1, -1 do bytes[i + m] = bytes[i] end
	for i = 1, m do bytes[off0 + i] = inserted[i] end
end

local function delete_range(bytes, off0, size)
	if size <= 0 then return end
	local n = #bytes
	for i = off0 + size + 1, n do bytes[i - size] = bytes[i] end
	for i = n - size + 1, n do bytes[i] = nil end
end

local function zeroes(n)
	local z = {}
	for i = 1, n do z[i] = 0 end
	return z
end

local function parse_elf(bytes)
	if #bytes < 0x34 or bytes[1] ~= 0x7f or bytes[2] ~= 0x45 or bytes[3] ~= 0x4c or bytes[4] ~= 0x46 then
		error("not an ELF file")
	end
	local class = bytes[5]
	local data = bytes[6]
	if class ~= 1 and class ~= 2 then error("unsupported ELF class") end
	if data ~= 1 and data ~= 2 then error("unsupported ELF endianness") end

	local elf = {
		bytes = bytes,
		class = class,
		bits = class == 1 and 32 or 64,
		endian = data == 1 and "little" or "big",
	}
	elf.read_u, elf.write_u = make_rw(bytes, elf.endian)

	if elf.bits == 64 then
		elf.e_phoff_off, elf.e_shoff_off = 0x20, 0x28
		elf.e_phentsize_off, elf.e_phnum_off = 0x36, 0x38
		elf.e_shentsize_off, elf.e_shnum_off, elf.e_shstrndx_off = 0x3a, 0x3c, 0x3e
		elf.sh_size = 64
		elf.ph_size = 56
	else
		elf.e_phoff_off, elf.e_shoff_off = 0x1c, 0x20
		elf.e_phentsize_off, elf.e_phnum_off = 0x2a, 0x2c
		elf.e_shentsize_off, elf.e_shnum_off, elf.e_shstrndx_off = 0x2e, 0x30, 0x32
		elf.sh_size = 40
		elf.ph_size = 32
	end
	elf.e_phoff = elf.read_u(elf.e_phoff_off, elf.bits == 64 and 8 or 4)
	elf.e_shoff = elf.read_u(elf.e_shoff_off, elf.bits == 64 and 8 or 4)
	elf.e_phentsize = elf.read_u(elf.e_phentsize_off, 2)
	elf.e_phnum = elf.read_u(elf.e_phnum_off, 2)
	elf.e_shentsize = elf.read_u(elf.e_shentsize_off, 2)
	elf.e_shnum = elf.read_u(elf.e_shnum_off, 2)
	elf.e_shstrndx = elf.read_u(elf.e_shstrndx_off, 2)
	if elf.e_shoff == 0 or elf.e_shnum == 0 then error("ELF has no section table") end
	if elf.e_shentsize ~= elf.sh_size then error("unsupported section header entry size") end
	if elf.e_phnum > 0 and elf.e_phentsize ~= elf.ph_size then error("unsupported program header entry size") end

	local function ph_field_base(idx)
		return elf.e_phoff + idx * elf.e_phentsize
	end
	local function read_ph(idx)
		local b = ph_field_base(idx)
		local ph = { index = idx }
		ph.type = elf.read_u(b, 4)
		if elf.bits == 64 then
			ph.flags = elf.read_u(b + 4, 4)
			ph.offset = elf.read_u(b + 8, 8)
			ph.vaddr = elf.read_u(b + 16, 8)
			ph.paddr = elf.read_u(b + 24, 8)
			ph.filesz = elf.read_u(b + 32, 8)
			ph.memsz = elf.read_u(b + 40, 8)
			ph.align = elf.read_u(b + 48, 8)
		else
			ph.offset = elf.read_u(b + 4, 4)
			ph.vaddr = elf.read_u(b + 8, 4)
			ph.paddr = elf.read_u(b + 12, 4)
			ph.filesz = elf.read_u(b + 16, 4)
			ph.memsz = elf.read_u(b + 20, 4)
			ph.flags = elf.read_u(b + 24, 4)
			ph.align = elf.read_u(b + 28, 4)
		end
		return ph
	end
	elf.program_headers = {}
	elf.protected_file_end = 0
	if elf.e_phnum > 0 then
		elf.protected_file_end = math.max(elf.protected_file_end,
			elf.e_phoff + elf.e_phnum * elf.e_phentsize)
	end
	for i = 0, elf.e_phnum - 1 do
		local ph = read_ph(i)
		elf.program_headers[#elf.program_headers + 1] = ph
		if (ph.filesz or 0) > 0 then elf.protected_file_end = math.max(elf.protected_file_end, ph.offset + ph.filesz) end
	end

	local function sh_field_base(idx)
		return elf.e_shoff + idx * elf.e_shentsize
	end
	local function read_sh(idx)
		local b = sh_field_base(idx)
		local sh = { index = idx, header_offset = b }
		sh.name_off = elf.read_u(b, 4)
		sh.type = elf.read_u(b + 4, 4)
		if elf.bits == 64 then
			sh.flags = elf.read_u(b + 8, 8)
			sh.addr = elf.read_u(b + 16, 8)
			sh.offset = elf.read_u(b + 24, 8)
			sh.size = elf.read_u(b + 32, 8)
			sh.link = elf.read_u(b + 40, 4)
			sh.info = elf.read_u(b + 44, 4)
			sh.addralign = elf.read_u(b + 48, 8)
			sh.entsize = elf.read_u(b + 56, 8)
		else
			sh.flags = elf.read_u(b + 8, 4)
			sh.addr = elf.read_u(b + 12, 4)
			sh.offset = elf.read_u(b + 16, 4)
			sh.size = elf.read_u(b + 20, 4)
			sh.link = elf.read_u(b + 24, 4)
			sh.info = elf.read_u(b + 28, 4)
			sh.addralign = elf.read_u(b + 32, 4)
			sh.entsize = elf.read_u(b + 36, 4)
		end
		return sh
	end
	elf.sections = {}
	for i = 0, elf.e_shnum - 1 do elf.sections[#elf.sections + 1] = read_sh(i) end
	local shstr = elf.sections[elf.e_shstrndx + 1]
	if shstr then
		for _, sh in ipairs(elf.sections) do sh.name = read_cstr(bytes, shstr.offset + sh.name_off) end
	end
	return elf
end
M.parse_elf = parse_elf

local function write_elf_header_counts(elf)
	elf.write_u(elf.e_shoff_off, elf.bits == 64 and 8 or 4, elf.e_shoff)
	elf.write_u(elf.e_shnum_off, 2, elf.e_shnum)
	elf.write_u(elf.e_shstrndx_off, 2, elf.e_shstrndx)
end

local function write_sh(elf, idx, sh)
	local b = elf.e_shoff + idx * elf.e_shentsize
	elf.write_u(b, 4, sh.name_off or 0)
	elf.write_u(b + 4, 4, sh.type or 0)
	if elf.bits == 64 then
		elf.write_u(b + 8, 8, sh.flags or 0)
		elf.write_u(b + 16, 8, sh.addr or 0)
		elf.write_u(b + 24, 8, sh.offset or 0)
		elf.write_u(b + 32, 8, sh.size or 0)
		elf.write_u(b + 40, 4, sh.link or 0)
		elf.write_u(b + 44, 4, sh.info or 0)
		elf.write_u(b + 48, 8, sh.addralign or 1)
		elf.write_u(b + 56, 8, sh.entsize or 0)
	else
		elf.write_u(b + 8, 4, sh.flags or 0)
		elf.write_u(b + 12, 4, sh.addr or 0)
		elf.write_u(b + 16, 4, sh.offset or 0)
		elf.write_u(b + 20, 4, sh.size or 0)
		elf.write_u(b + 24, 4, sh.link or 0)
		elf.write_u(b + 28, 4, sh.info or 0)
		elf.write_u(b + 32, 4, sh.addralign or 1)
		elf.write_u(b + 36, 4, sh.entsize or 0)
	end
end

local function shift_model(elf, at, delta)
	if elf.e_shoff >= at then elf.e_shoff = elf.e_shoff + delta end
	for _, sh in ipairs(elf.sections) do
		if sh.type ~= SHT_NOBITS and sh.offset >= at and sh.size > 0 then sh.offset = sh.offset + delta end
	end
end

local function refresh_all_headers(elf)
	write_elf_header_counts(elf)
	for i, sh in ipairs(elf.sections) do
		sh.index = i - 1
		write_sh(elf, i - 1, sh)
	end
end

local function normalize_perms(perms)
	perms = string.upper(perms or "")
	local seen = { R = false, W = false, X = false, A = false }
	for c in perms:gmatch(".") do if seen[c] ~= nil then seen[c] = true end end
	local out = {}
	if seen.R then out[#out + 1] = "R" end
	if seen.W then out[#out + 1] = "W" end
	if seen.X then out[#out + 1] = "X" end
	if seen.A then out[#out + 1] = "A" end
	return #out > 0 and table.concat(out) or "R"
end

local function permission_flags(perms)
	perms = normalize_perms(perms)
	local flags = (perms:find("R", 1, true) or perms:find("A", 1, true)) and SHF_ALLOC or 0
	if perms:find("W", 1, true) then flags = flags | SHF_WRITE end
	if perms:find("X", 1, true) then flags = flags | SHF_EXECINSTR end
	return flags
end
M.permission_flags = permission_flags

function M.section_permissions(sh)
	local writable = (sh.flags & SHF_WRITE) ~= 0
	local executable = (sh.flags & SHF_EXECINSTR) ~= 0
	local alloc = (sh.flags & SHF_ALLOC) ~= 0
	local readable = alloc or (not writable and not executable)
	local out = {}
	out[#out + 1] = readable and "R" or "-"
	out[#out + 1] = writable and "W" or "-"
	out[#out + 1] = executable and "X" or "-"
	out[#out + 1] = alloc and "A" or "-"
	return table.concat(out)
end

local function section_color(sh)
	local readable = (sh.flags & SHF_ALLOC) ~= 0
	local writable = (sh.flags & SHF_WRITE) ~= 0
	local executable = (sh.flags & SHF_EXECINSTR) ~= 0
	if readable and writable and executable then return "Magenta" end
	if executable then return "Red" end
	if readable and writable then return "Blue" end
	return "White"
end
M.section_color = section_color

local function section_data_end(sh)
	if not sh or sh.type == SHT_NOBITS or sh.size == 0 then return nil end
	return sh.offset + sh.size
end

local function program_headers_file_end(elf)
	if elf.protected_file_end then return elf.protected_file_end end
	local protected_end = 0
	if elf.e_phnum and elf.e_phnum > 0 then
		protected_end = math.max(protected_end, elf.e_phoff + elf.e_phnum * elf.e_phentsize)
	end
	for _, ph in ipairs(elf.program_headers or {}) do
		if (ph.filesz or 0) > 0 then protected_end = math.max(protected_end, ph.offset + ph.filesz) end
	end
	elf.protected_file_end = protected_end
	return protected_end
end
M.program_headers_file_end = program_headers_file_end

local function ensure_insert_does_not_shift_program_data(elf, off0, delta, reason)
	if delta <= 0 then return end
	local protected_end = program_headers_file_end(elf)
	if off0 < protected_end then
		error(string.format("cannot %s at %#x: it would shift program-header-backed data before %#x", reason, off0,
			protected_end))
	end
end

local function metadata_insert_offset(elf, align)
	ensure_insert_does_not_shift_program_data(elf, elf.e_shoff, 1, "grow the section header table")
	return align_up(elf.e_shoff, align)
end

local function update_section_index_references(elf, new_index)
	for _, sh in ipairs(elf.sections) do
		if (sh.link or 0) >= new_index then sh.link = sh.link + 1 end
		if (sh.type == SHT_REL or sh.type == SHT_RELA) and (sh.info or 0) >= new_index then sh.info = sh.info + 1 end
	end
end

local function update_symbol_section_indices(elf, new_index)
	local shndx_off = elf.bits == 64 and 6 or 14
	for _, sh in ipairs(elf.sections) do
		if (sh.type == SHT_SYMTAB or sh.type == SHT_DYNSYM) and sh.type ~= SHT_NOBITS and (sh.entsize or 0) > shndx_off then
			local count = math.floor((sh.size or 0) / sh.entsize)
			for i = 0, count - 1 do
				local off = sh.offset + i * sh.entsize + shndx_off
				local st_shndx = elf.read_u(off, 2)
				if st_shndx >= new_index and st_shndx < SHN_LORESERVE then elf.write_u(off, 2, st_shndx + 1) end
			end
		end
	end
end

function M.add_section(original, opts)
	opts = opts or {}
	local bytes = clone_bytes(original)
	local elf = parse_elf(bytes)
	local name = opts.name or DEFAULT_NAME
	if name:sub(1, 1) ~= "." then name = "." .. name end
	local size = math.max(math.floor(parse_integer(opts.size, 0) or 0), 0)
	local align = math.max(math.floor(parse_integer(opts.align, 1) or 1), 1)
	local perms = normalize_perms(opts.perms or opts.permissions or "RW")
	local content = opts.content or zeroes(size)
	size = #content

	local after_index = tonumber(opts.after_index)
	if not after_index then after_index = elf.e_shnum - 1 end
	if after_index < 0 or after_index >= elf.e_shnum then error("invalid insertion section index") end
	local new_index = after_index + 1

	local shstr = elf.sections[elf.e_shstrndx + 1]
	if not shstr or shstr.type == SHT_NOBITS then error("missing usable section-name string table") end

	local shifts = {}
	local name_off = shstr.size
	local name_bytes = { string.byte(name, 1, #name) }
	name_bytes[#name_bytes + 1] = 0
	local name_insert_at = shstr.offset + shstr.size
	ensure_insert_does_not_shift_program_data(elf, name_insert_at, #name_bytes, "append the section name")
	insert_bytes(bytes, name_insert_at, name_bytes)
	shstr.size = shstr.size + #name_bytes
	shift_model(elf, name_insert_at, #name_bytes)
	shifts[#shifts + 1] = { offset = name_insert_at, delta = #name_bytes, reason = "append section name to .shstrtab" }
	refresh_all_headers(elf)

	local base = metadata_insert_offset(elf, 1)
	local data_off = metadata_insert_offset(elf, align)
	local pad = data_off - base
	if pad > 0 then
		ensure_insert_does_not_shift_program_data(elf, base, pad, "insert alignment padding before the new section")
		insert_bytes(bytes, base, zeroes(pad))
		shift_model(elf, base, pad)
		shifts[#shifts + 1] = { offset = base, delta = pad, reason = "alignment padding before new section data" }
		refresh_all_headers(elf)
	end

	ensure_insert_does_not_shift_program_data(elf, data_off, #content, "insert new section contents")
	insert_bytes(bytes, data_off, content)
	shift_model(elf, data_off, #content)
	shifts[#shifts + 1] = { offset = data_off, delta = #content, reason = "insert new section contents in metadata area" }

	local new_sh = {
		name_off = name_off,
		type = 1,
		flags = permission_flags(perms),
		addr = 0,
		offset = data_off,
		size = size,
		link = 0,
		info = 0,
		addralign = align,
		entsize = 0,
		name = name,
	}

	update_section_index_references(elf, new_index)
	update_symbol_section_indices(elf, new_index)

	local header_at = elf.e_shoff + new_index * elf.e_shentsize
	ensure_insert_does_not_shift_program_data(elf, header_at, elf.e_shentsize, "insert the section header")
	table.insert(elf.sections, new_index + 1, new_sh)
	elf.e_shnum = elf.e_shnum + 1
	if elf.e_shstrndx >= new_index then elf.e_shstrndx = elf.e_shstrndx + 1 end
	insert_bytes(bytes, header_at, zeroes(elf.e_shentsize))
	shift_model(elf, header_at, elf.e_shentsize)
	shifts[#shifts + 1] = {
		offset = header_at,
		delta = elf.e_shentsize,
		reason = "insert section header after highlighted section"
	}
	refresh_all_headers(elf)

	return bytes, {
		action = "add",
		name = name,
		after_index = after_index,
		new_index = new_index,
		size_delta = #bytes - #original,
		name_offset = name_insert_at,
		section_offset = new_sh.offset,
		section_size = size,
		section_header_offset = header_at,
		permissions = perms,
		shifts = shifts,
	}
end

function M.remove_section(original, selector)
	local bytes = clone_bytes(original)
	local elf = parse_elf(bytes)
	local idx = nil
	if type(selector) == "number" then
		idx = selector
	else
		for i, sh in ipairs(elf.sections) do
			if sh.name == selector then
				idx = i - 1
				break
			end
		end
	end
	if not idx or idx <= 0 or idx >= elf.e_shnum then error("invalid or protected section index") end
	local removed = elf.sections[idx + 1]
	local shifts = {}

	if removed.type ~= SHT_NOBITS and removed.size > 0 then
		delete_range(bytes, removed.offset, removed.size)
		shift_model(elf, removed.offset + removed.size, -removed.size)
		shifts[#shifts + 1] = { offset = removed.offset, delta = -removed.size, reason = "remove section contents" }
	end

	local header_at = elf.e_shoff + idx * elf.e_shentsize
	delete_range(bytes, header_at, elf.e_shentsize)
	table.remove(elf.sections, idx + 1)
	elf.e_shnum = elf.e_shnum - 1
	if elf.e_shstrndx == idx then elf.e_shstrndx = 0 elseif elf.e_shstrndx > idx then elf.e_shstrndx = elf.e_shstrndx - 1 end
	shifts[#shifts + 1] = { offset = header_at, delta = -elf.e_shentsize, reason = "remove section header" }
	refresh_all_headers(elf)

	return bytes, {
		action = "remove",
		name = removed.name or ("#" .. idx),
		index = idx,
		size_delta = #bytes - #original,
		section_offset = removed.offset,
		section_size = removed.size,
		section_header_offset = header_at,
		shifts = shifts,
	}
end

local function sections_from_context(context)
	local ok, elf = pcall(parse_elf, bytes_from_context(context))
	if not ok then return nil, elf end
	return elf.sections, nil
end

local function setting(context, key, default)
	local ok, value = pcall(function() return context.settings:get_custom(key) end)
	if ok and value ~= nil then return value end
	return default
end

local function operation_opts(context)
	return {
		name = setting(context, "elf_section_name", DEFAULT_NAME),
		size = tostring(setting(context, "elf_section_size", DEFAULT_SIZE)),
		perms = normalize_perms(setting(context, "elf_section_perms", "RW")),
		align = tostring(setting(context, "elf_section_align", DEFAULT_ALIGN)),
	}
end

local function write_file(path, bytes)
	local f, err = io.open(path, "wb")
	if not f then return nil, err end
	local chunk = {}
	local chunk_size = 8192
	for i = 1, #bytes do
		chunk[#chunk + 1] = string.char(bytes[i])
		if #chunk == chunk_size then
			f:write(table.concat(chunk))
			chunk = {}
		end
	end
	if #chunk > 0 then f:write(table.concat(chunk)) end
	f:close()
	return true
end

local function perform(context, op)
	local output, summary = op.output, op.preview
	if not output or not summary then
		local input = bytes_from_context(context)
		local ok
		ok, output, summary = pcall(function()
			if op.action == "add" then return M.add_section(input, op.opts) end
			return M.remove_section(input, op.index)
		end)
		if not ok then
			context.log(3, "ELF section edit failed: " .. tostring(output)); return
		end
	end

	local len = context.data.len
	if type(len) == "function" then len = context.data:len() end
	if #output ~= len then
		if not op.output_path or op.output_path == "" then
			UI.pending = op
			UI.mode = "save_path"
			UI.save_path = UI.save_path ~= "" and UI.save_path or "patched.elf"
			return
		end
		local wrote, err = write_file(op.output_path, output)
		if not wrote then
			context.log(3, "Could not write resized ELF to " .. op.output_path .. ": " .. tostring(err)); return
		end
		context.log(1, "Wrote resized ELF to " .. op.output_path .. " (" .. summary.size_delta .. " bytes delta)")
	else
		local applied, reason = apply_bytes_to_context(context, output)
		if not applied then
			context.log(3, reason); return
		end
		context.log(1, "Applied ELF section edit in-place")
	end
	UI.mode = "list"
	UI.pending = nil
	UI.add_form = nil
	UI.message = "Last operation: " .. summary.action .. " " .. summary.name .. ", delta " .. summary.size_delta
end

local function selected_section()
	return UI.sections[math.min(UI.selected, #UI.sections)]
end

local function format_field_line(label, value)
	return string.format("  %-13s  %-36s", label .. ":", tostring(value or ""))
end
M.format_field_line = format_field_line

local function draw_field(popup, label, value, active, color)
	if active then
		popup.text:set_style({ fg = "Black", bg = "White", add_modifier = BOLD })
		popup.text:push_line(format_field_line(label, value))
		popup.text:reset_style()
	else
		popup.text:set_style({ fg = color or "White", add_modifier = BOLD })
		popup.text:push_span(string.format("  %-13s  ", label .. ":"))
		popup.text:reset_style()
		popup.text:push_line(string.format("%-36s", tostring(value or "")))
	end
end

function init(context)
	context.add_command("elf_sections", "Open ELF section editor")
end

function elf_sections(context)
	UI.selected = 1
	UI.mode = "list"
	UI.pending = nil
	UI.add_form = nil
	context.open_popup("elf_sections_popup")
end

function elf_sections_popup(popup, context)
	local sections, err = sections_from_context(context)
	UI.sections = sections or {}
	popup.title:set("ELF Sections")
	popup.width:set(math.min(math.max(82, math.floor(context.screen_width * 0.8)), context.screen_width))
	popup.height:set(math.min(math.max(14, #UI.sections + 10), context.screen_height))

	if err then
		popup.text:push_line("Not an editable ELF: " .. tostring(err))
		popup.text:push_line("Esc closes this popup.")
		return
	end
	if UI.selected > #UI.sections then UI.selected = #UI.sections end
	if UI.selected < 1 then UI.selected = 1 end

	if UI.mode == "add_form" and UI.add_form then
		popup.text:set_style({ fg = "Black", bg = "Cyan", add_modifier = BOLD })
		popup.text:push_line(string.format(" Add section after %-28s #%d ", UI.add_form.after_name or "<unknown>",
			UI.add_form.after_index))
		popup.text:reset_style()
		popup.text:set_style({ fg = "DarkGray" })
		popup.text:push_line(" Tab/Up/Down moves fields · Backspace edits · Enter previews diff · Esc cancels")
		popup.text:reset_style()
		popup.text:push_line("")
		draw_field(popup, "Name", UI.add_form.name, UI.add_form.field == 1, "LightCyan")
		draw_field(popup, "Permissions", UI.add_form.perms, UI.add_form.field == 2, "LightMagenta")
		draw_field(popup, "Size", UI.add_form.size .. " bytes", UI.add_form.field == 3, "LightGreen")
		draw_field(popup, "Alignment", UI.add_form.align .. " bytes", UI.add_form.field == 4, "LightYellow")
		popup.text:push_line("")
		popup.text:set_style({ fg = "Gray" })
		popup.text:push_line(" Permissions accept R, W, X, A. Examples: R, RW, RX, RWX.")
		popup.text:reset_style()
		return
	end

	if UI.mode == "save_path" and UI.pending then
		local p = UI.pending.preview
		popup.text:set_style({ fg = "Black", bg = "Yellow", add_modifier = BOLD })
		popup.text:push_line(" Resized ELF output path required ")
		popup.text:reset_style()
		popup.text:push_line("Operation changes file size by " ..
			p.size_delta .. " bytes; HexPatch Lua cannot resize the open buffer.")
		popup.text:push_line("")
		draw_field(popup, "Save as", UI.save_path, true, "LightGreen")
		popup.text:push_line("")
		popup.text:push_line("Enter: write new ELF   Esc: cancel   Backspace/type: edit path")
		return
	end

	if UI.mode == "confirm" and UI.pending then
		local p = UI.pending.preview
		popup.text:set_style({ fg = "Yellow", add_modifier = BOLD })
		popup.text:push_line("Confirm " .. p.action .. " section: " .. p.name)
		popup.text:reset_style()
		popup.text:push_line("Total size delta: " .. p.size_delta .. " bytes")
		if p.action == "add" then
			popup.text:push_line("New section index: " ..
				p.new_index .. "  after index: " .. p.after_index .. "  perms: " .. p.permissions)
		end
		for _, s in ipairs(p.shifts or {}) do
			popup.text:push_line(string.format("  %#x %+d  %s", s.offset, s.delta, s.reason))
		end
		popup.text:push_line("")
		popup.text:push_line("Enter/y: confirm   Esc/n: cancel")
		return
	end

	popup.text:push_line("Use Up/Down. Insert/I adds after highlighted. Delete/d removes. Esc closes.")
	if UI.message then popup.text:push_line(UI.message) end
	popup.text:push_line("")
	popup.text:set_style({ fg = "Black", bg = "Gray", add_modifier = BOLD })
	popup.text:push_line(string.format(" %3s  %-24s  %12s  %12s  %-5s ", "Idx", "Name", "Offset", "Size", "Perm"))
	popup.text:reset_style()
	for i, sh in ipairs(UI.sections) do
		local style = { fg = section_color(sh) }
		if UI.selected == i then
			style.bg = "DarkGray"; style.add_modifier = BOLD
		end
		popup.text:set_style(style)
		popup.text:push_line(string.format(" %3d  %-24s  0x%010x  0x%010x  %-5s ", sh.index, sh.name or "",
			sh.offset or 0,
			sh.size or 0, M.section_permissions(sh)))
		popup.text:reset_style()
	end
end

local function preview_pending(context, op)
	local input = bytes_from_context(context)
	local ok, output, summary = pcall(function()
		if op.action == "add" then return M.add_section(input, op.opts) end
		return M.remove_section(input, op.index)
	end)
	if not ok then
		context.log(3, "ELF section preview failed: " .. tostring(output)); return
	end
	op.output = output
	op.preview = summary
	UI.pending = op
	UI.mode = "confirm"
end

local function start_add_form(context)
	local sh = selected_section()
	if not sh then return end
	local opts = operation_opts(context)
	UI.add_form = {
		field = 1,
		name = opts.name,
		perms = opts.perms,
		size = opts.size,
		align = opts.align,
		after_index = sh.index,
		after_name = sh.name or "",
	}
	UI.mode = "add_form"
end

local function form_to_opts(form)
	return {
		name = form.name ~= "" and form.name or DEFAULT_NAME,
		perms = normalize_perms(form.perms),
		size = math.max(math.floor(parse_integer(form.size, 0) or 0), 0),
		align = math.max(math.floor(parse_integer(form.align, 1) or 1), 1),
		after_index = form.after_index,
	}
end

local function edit_save_path_key(key, context)
	if key.code == "Esc" then
		UI.mode = "list"
		UI.pending = nil
		return
	end
	if key.code == "Enter" then
		if UI.pending then
			UI.pending.output_path = UI.save_path
			perform(context, UI.pending)
		end
		return
	end
	if key.code == "Backspace" then
		UI.save_path = UI.save_path:sub(1, -2)
		return
	end
	if #key.code == 1 then UI.save_path = UI.save_path .. key.code end
end

local function edit_form_key(key, context)
	local form = UI.add_form
	if not form then return end
	if key.code == "Esc" then
		UI.mode = "list"; UI.add_form = nil; return
	end
	if key.code == "Enter" then
		preview_pending(context, { action = "add", opts = form_to_opts(form) })
		return
	end
	local field = tonumber(form.field) or 1
	if key.code == "Tab" or key.code == "Down" then
		form.field = field % 4 + 1; return
	end
	if key.code == "BackTab" or key.code == "Up" then
		form.field = (field + 2) % 4 + 1; return
	end

	local names = { "name", "perms", "size", "align" }
	local active = names[field]
	if not active then return end
	local current = tostring(form[active] or "")
	if key.code == "Backspace" then
		form[active] = current:sub(1, -2)
		return
	end
	if #key.code == 1 then
		local c = key.code
		if active == "perms" then
			c = string.upper(c)
			if not c:match("[RWXA]") then return end
		elseif active == "size" or active == "align" then
			if not c:match("[0-9a-fA-FxX]") then return end
		end
		form[active] = current .. c
	end
end

function on_key(key, context)
	if context.get_popup() ~= "elf_sections_popup" or key.kind == "Release" then return end
	if UI.mode == "confirm" then
		if key.code == "Enter" or key.code == "y" or key.code == "Y" then
			perform(context, UI.pending)
		elseif key.code == "Esc" or key.code == "n" or key.code == "N" then
			UI.mode = "list"; UI.pending = nil
		end
		return
	end
	if UI.mode == "save_path" then
		edit_save_path_key(key, context); return
	end
	if UI.mode == "add_form" then
		edit_form_key(key, context); return
	end

	local max = #UI.sections
	if key.code == "Down" then
		UI.selected = math.min(UI.selected + 1, max)
	elseif key.code == "Up" then
		UI.selected = math.max(UI.selected - 1, 1)
	elseif key.code == "Esc" then
		context.close_popup("elf_sections_popup")
	elseif key.code == "Insert" or key.code == "i" or key.code == "I" then
		start_add_form(context)
	elseif key.code == "Delete" or key.code == "d" or key.code == "D" then
		local sh = selected_section()
		if sh and sh.index > 0 then preview_pending(context, { action = "remove", index = sh.index }) end
	end
end

return M
