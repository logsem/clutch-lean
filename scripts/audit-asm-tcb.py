#!/usr/bin/env python3
"""Audit a theorem's statement definitions and source coverage (python3 -I)."""

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tempfile


def run(arguments, project):
    result = subprocess.run(arguments, cwd=project, text=True, capture_output=True, timeout=600)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def source_origin(declaration, declarations, source):
    """Locate a declaration or the source command that generated it."""
    parent = declaration
    while parent:
        if parent in declarations:
            return declarations[parent], parent != declaration
        parent = parent.rsplit(".", 1)[0] if "." in parent else ""
    match = re.match(r"^(.*\.)?inst(?:DecidableEq|BEq|Repr|Inhabited)([^.]+)", declaration)
    if match:
        owner = (match[1] or "") + match[2]
        if owner in declarations:
            return declarations[owner], True
    if source:
        for line, text in enumerate(source.splitlines(), 1):
            match = re.search(r"deriving\s+instance\s+MeasurableSpace\s+for\s+(\w+)", text)
            if match and f".{match[1]}." in declaration:
                return [line, 0, line, len(text)], True
    return None, False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("theorem")
    parser.add_argument("--project", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    for name in [args.module, args.theorem]:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name):
            raise ValueError("expected an ordinary Lean module or declaration name")
    project = args.project.resolve()
    run(["lake", "build", args.module], project)
    imports = {args.module}
    with tempfile.TemporaryDirectory(prefix="asm-tcb-") as directory:
        source = pathlib.Path(directory) / "Audit.lean"
        while True:
            # Legacy import mode exposes private data and accepts both module formats.
            source.write_text("".join(f"import {module}\n" for module in sorted(imports))
                              + f"import Metrology.Meta.TCB\n#tcb {args.theorem}\n")
            output = run(["lake", "env", "lean", str(source)], project)
            receipts = re.findall(r"TCBJSON (\{[^\n]*\})", output)
            if len(receipts) != 1:
                raise ValueError("expected one TCB receipt; compiler output:\n" + output)
            receipt = json.loads(receipts[0])
            discovered = {group["module"] for group in receipt["groups"]}
            if discovered <= imports:
                break
            imports |= discovered
    lean_path = run(["lake", "env", "printenv", "LEAN_PATH"], project).strip().split(":")
    search = [project / path for path in lean_path]
    for group in receipt["groups"]:
        relative = pathlib.Path(*group["module"].split(".")).with_suffix(".ilean")
        ilean = next((base / relative for base in search if (base / relative).is_file()), None)
        declarations = json.loads(ilean.read_text())["decls"] if ilean else {}
        root = next((parent for parent in ilean.parents
                     if (parent / "lakefile.toml").is_file() or (parent / "lakefile.lean").is_file()),
                    None) if ilean else None
        source_path = root / relative.with_suffix(".lean") if root else None
        source = source_path.read_text() if source_path and source_path.is_file() else None
        lines, missing, generated = set(), [], []
        for declaration in group["declarations"]:
            bounds, is_generated = source_origin(declaration, declarations, source)
            if bounds:
                lines.update(range(bounds[0], bounds[2] + 1))
                if is_generated:
                    generated.append(declaration)
            else:
                missing.append(declaration)
        group["source_lines"] = len(lines)
        group["generated_declarations"] = generated
        group["source"] = str(source_path) if source else None
        group["source_sha256"] = hashlib.sha256(source.encode()).hexdigest() if source else None
        group["missing_ranges"] = missing
        group["ilean"] = str(ilean) if ilean else None
    receipt["complete"] = not receipt["unavailable_bodies"] and all(
        not group["missing_ranges"] for group in receipt["groups"])
    receipt["built_module"] = args.module
    encoded = json.dumps(receipt, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")
    if not receipt["complete"]:
        raise SystemExit("incomplete statement audit: missing bodies or source ranges")


if __name__ == "__main__":
    main()
