-- Regression tests for plugins/elf_section_editor.lua.
-- Kept outside plugins/ so plugin-folder loading does not execute tests.
-- Run from the repository root with:
--   lua test/elf_section_editor_tests.lua

package.path = "plugins/?.lua;" .. package.path

local editor = require("elf_section_editor")

local fixture = arg and arg[1] or "test/elf.bin"
local output_path = "/tmp/hexpatch_elf_section_editor_test.elf"

local function fail(message)
	error(message, 2)
end

local function assert_eq(actual, expected, message)
	if actual ~= expected then
		fail(string.format("%s: expected %s, got %s", message or "assert_eq failed", tostring(expected), tostring(actual)))
	end
end

local function assert_true(value, message)
	if not value then fail(message or "assert_true failed") end
end

local function read_bytes(path)
	local f = assert(io.open(path, "rb"))
	local s = f:read("a")
	f:close()
	local bytes = {}
	for i = 1, #s do bytes[i] = s:byte(i) end
	return bytes
end

local function write_bytes(path, bytes)
	local f = assert(io.open(path, "wb"))
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
end

local function find_section(elf, name)
	for _, sh in ipairs(elf.sections) do
		if sh.name == name then return sh end
	end
	return nil
end

local function command_ok(command)
	local ok = os.execute(command)
	return ok == true or ok == 0
end

local function allow_range(allowed, off0, size)
	for off = off0, off0 + size - 1 do allowed[off] = true end
end

local function elf_section_metadata_offsets(elf)
	local allowed = {}
	allow_range(allowed, elf.e_shoff_off, elf.bits == 64 and 8 or 4)
	allow_range(allowed, elf.e_shnum_off, 2)
	allow_range(allowed, elf.e_shstrndx_off, 2)
	return allowed
end

local function assert_range_unchanged(original, patched, off0, size, label, allowed_offsets)
	for i = off0 + 1, off0 + size do
		if original[i] ~= patched[i] and not (allowed_offsets and allowed_offsets[i - 1]) then
			fail(string.format("%s changed at file offset %#x", label, i - 1))
		end
	end
end

local function test_add_after_text_preserves_runtime_image()
	local original_bytes = read_bytes(fixture)
	local original = editor.parse_elf(original_bytes)
	local text = assert(find_section(original, ".text"), "fixture must contain .text")
	local text_index = assert(tonumber(text.index), ".text section is missing an index")

	local content = { 0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe, 0, 1, 2, 3, 4, 5, 6, 7 }
	local patched_bytes, summary = editor.add_section(original_bytes, {
		name = ".after_text",
		content = content,
		perms = "RW",
		align = "0x10",
		after_index = text_index,
	})
	if not patched_bytes then fail("add_section did not return patched bytes") end
	if not summary then fail("add_section did not return a summary") end
	local patched = editor.parse_elf(patched_bytes)
	local inserted = patched.sections[text_index + 2]
	if not inserted then fail("new section was not inserted after .text") end
	local inserted_offset = inserted.offset
	if inserted_offset == nil then fail("new section is missing an offset") end
	local summary_new_index = summary.new_index
	if summary_new_index == nil then fail("summary is missing the new section index") end

	assert_eq(patched.e_shnum, original.e_shnum + 1, "section count")
	assert_eq(summary_new_index, text_index + 1, "new section index")
	assert_eq(inserted.name, ".after_text", "new section placement in section table")
	assert_eq(inserted.size, #content, "new section size")
	assert_eq(inserted_offset % 16, 0, "new section alignment")
	for i, byte in ipairs(content) do
		assert_eq(patched_bytes[inserted_offset + i], byte, "new section content")
	end

	local protected_end = editor.program_headers_file_end(original)
	assert_true(inserted_offset >= protected_end,
		string.format("new section data offset %#x must not be inside program-header-backed data ending at %#x",
			inserted_offset, protected_end))

	local allowed_runtime_header_changes = elf_section_metadata_offsets(original)
	for _, ph in ipairs(original.program_headers) do
		if (ph.filesz or 0) > 0 then
			assert_range_unchanged(original_bytes, patched_bytes, ph.offset, ph.filesz,
				string.format("program header #%d file image", ph.index), allowed_runtime_header_changes)
		end
	end

	local symtab = assert(find_section(patched, ".symtab"), "fixture must contain .symtab")
	assert(find_section(patched, ".strtab"), "fixture must contain .strtab")
	local symtab_link = assert(tonumber(symtab.link), ".symtab is missing sh_link")
	local linked_strtab = patched.sections[symtab_link + 1]
	if not linked_strtab then fail(".symtab sh_link points outside the section table") end
	assert_eq(linked_strtab.name, ".strtab", ".symtab sh_link")

	local rela_plt = find_section(patched, ".rela.plt")
	if rela_plt then
		local rela_info = rela_plt.info
		if rela_info == nil then fail(".rela.plt is missing sh_info") end
		local rela_target = patched.sections[rela_info + 1]
		if not rela_target then fail(".rela.plt sh_info points outside the section table") end
		assert_eq(rela_target.name, ".got", ".rela.plt sh_info target")
	end

	write_bytes(output_path, patched_bytes)
	assert_true(command_ok("chmod +x /tmp/hexpatch_elf_section_editor_test.elf"), "chmod patched ELF")
	assert_true(
		command_ok(
			"readelf -S -l /tmp/hexpatch_elf_section_editor_test.elf >/tmp/hexpatch_elf_section_editor_test.readelf 2>/tmp/hexpatch_elf_section_editor_test.readelf.err"),
		"readelf accepts patched ELF")
	assert_true(
		command_ok(
			"/tmp/hexpatch_elf_section_editor_test.elf --help >/tmp/hexpatch_elf_section_editor_test.out 2>/tmp/hexpatch_elf_section_editor_test.err"),
		"patched ELF runs --help")
end

local function test_hex_size_and_alignment_input()
	assert_eq(editor.parse_integer("0x1000", 0), 4096, "lowercase hex parse")
	assert_eq(editor.parse_integer("0X20", 0), 32, "uppercase hex parse")
	assert_eq(editor.parse_integer("64", 0), 64, "decimal parse")
	assert_eq(editor.parse_integer("", 7), 7, "empty value default")

	local original_bytes = read_bytes(fixture)
	local original = editor.parse_elf(original_bytes)
	local text = assert(find_section(original, ".text"), "fixture must contain .text")
	local text_index = assert(tonumber(text.index), ".text section is missing an index")
	local patched_bytes = assert(editor.add_section(original_bytes, {
		name = ".hex_size",
		size = "0x20",
		perms = "RW",
		align = "0x10",
		after_index = text_index,
	}), "add_section did not return patched bytes")
	local patched = editor.parse_elf(patched_bytes)
	local inserted = assert(patched.sections[text_index + 2], "new section was not inserted after .text")
	local inserted_offset = assert(tonumber(inserted.offset), "new section is missing an offset")
	assert_eq(inserted.size, 0x20, "hex section size")
	assert_eq(inserted_offset % 0x10, 0, "hex section alignment")
end

local function test_popup_field_columns_are_aligned()
	local name_line = editor.format_field_line("Name", ".hexpatch")
	local perms_line = editor.format_field_line("Permissions", "RW")
	local align_line = editor.format_field_line("Alignment", "0x10 bytes")

	assert_eq(#name_line, #perms_line, "name and permissions rows have equal width")
	assert_eq(#align_line, #name_line, "alignment row width")
	assert_true(not name_line:find("< editing", 1, true), "field row must not include an edit marker")
	assert_true(not name_line:find("\n", 1, true), "field row must be a single line")
end

local tests = {
	{ name = "test_add_after_text_preserves_runtime_image", run = test_add_after_text_preserves_runtime_image },
	{ name = "test_hex_size_and_alignment_input",           run = test_hex_size_and_alignment_input },
	{ name = "test_popup_field_columns_are_aligned",        run = test_popup_field_columns_are_aligned },
}

for _, test in ipairs(tests) do
	test.run()
	print("PASS " .. test.name)
end
