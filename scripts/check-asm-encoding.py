#!/usr/bin/env python3
"""Compare Lean's assembled image with a linked LLVM RV64 image (python3 -I)."""

import argparse
import pathlib
import re
import struct
import subprocess
import tempfile


def elf_sections(path):
    """Read named ELF64 little-endian sections without external ELF tools."""
    data = path.read_bytes()
    if data[:6] != b"\x7fELF\x02\x01":
        raise ValueError("expected a little-endian ELF64 image")
    offset = struct.unpack_from("<Q", data, 40)[0]
    entry_size, count, names_index = struct.unpack_from("<HHH", data, 58)
    headers = [struct.unpack_from("<IIQQQQIIQQ", data, offset + i * entry_size)
               for i in range(count)]
    names_header = headers[names_index]
    names = data[names_header[4]:names_header[4] + names_header[5]]
    return {names[h[0]:].split(b"\0", 1)[0].decode():
            (h[3], data[h[4]:h[4] + h[5]]) for h in headers}


def run(args, cwd):
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True, timeout=120)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("--zig", required=True, type=pathlib.Path)
    args = parser.parse_args()
    repo = pathlib.Path(__file__).resolve().parent.parent
    source, zig = args.source.resolve(), args.zig.resolve()
    with tempfile.TemporaryDirectory(prefix="asm-encoding-") as name:
        tmp = pathlib.Path(name)
        raw, obj, elf = (tmp / name for name in ["image.bin", "image.o", "image.elf"])
        result = run(["lake", "env", "lean", "--run",
                      "Metrology/ProbLang/Asm/Assemble.lean", str(source), str(raw)], repo)
        print(result, end="")
        match = re.search(r"text=(\d+) rodata=(\d+)", result)
        if not match:
            raise ValueError("assembler did not report its image layout")
        text_length, rodata_offset = map(int, match.groups())
        cc = [str(zig), "cc", "-target", "riscv64-linux-musl",
              "-mcpu=baseline_rv64-c", "-mno-relax"]
        run(cc + ["-c", str(source), "-o", str(obj)], repo)
        script = tmp / "image.ld"
        script.write_text("SECTIONS { . = 0x10000; .text : { *(.text) } "
                          ". = ALIGN(8); .rodata : { *(.rodata*) } "
                          "/DISCARD/ : { *(.riscv.attributes) *(.comment) *(.note*) } }\n")
        run(cc + ["-nostdlib", "-static", "-Wl,-T," + str(script),
                  str(obj), "-o", str(elf)], repo)
        sections = elf_sections(elf)
        image = raw.read_bytes()
        text_address, text = sections[".text"]
        if len(text) != text_length:
            raise ValueError(f"text length differs: LLVM={len(text)}, Lean={text_length}")
        if text != image[:text_length]:
            diffs = [i for i, (a, b) in enumerate(zip(text, image)) if a != b]
            raise ValueError(f"text differs at offsets {diffs[:20]}")
        if ".rodata" in sections:
            address, rodata = sections[".rodata"]
            if address - text_address != rodata_offset:
                raise ValueError("read-only data placement differs")
            if rodata != image[rodata_offset:]:
                raise ValueError("read-only data contents differ")
        elif any(image[text_length:]):
            raise ValueError("unexpected nonzero bytes after text")
        print(f"PASS: {text_length} text bytes and read-only data match LLVM")


if __name__ == "__main__":
    main()
