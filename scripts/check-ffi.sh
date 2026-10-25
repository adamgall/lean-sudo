#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 - "$@" <<'PY'
import os
import pathlib
import re
import shlex
import subprocess
import sys
import tempfile


def fail(message):
    sys.exit("check-ffi: " + message)


def defined_functions(path, dynamic=False):
    command = ["nm", "-g", "--defined-only", "--format=posix"]
    if dynamic:
        command.append("-D")
    result = set()
    with subprocess.Popen(command + [str(path)], stdout=subprocess.PIPE, text=True) as process:
        for line in process.stdout:
            fields = line.split()
            if len(fields) >= 2 and fields[1] in ("T", "W", "i", "I"):
                result.add(fields[0].split("@", 1)[0])
        if process.wait():
            raise subprocess.CalledProcessError(process.returncode, command + [str(path)])
    return result


def main():
    root = pathlib.Path.cwd()
    symbols = set()
    attribute = re.compile(r'@\[([^\]]*)\]', re.DOTALL)
    external = re.compile(r'\bextern\s+"([A-Za-z_][A-Za-z_0-9]*)"')
    for source in sorted(root.rglob("*.lean")):
        if any(part.startswith(".") for part in source.relative_to(root).parts):
            continue
        for match in attribute.finditer(source.read_text()):
            symbols.update(external.findall(match[1]))
    if not symbols:
        fail("no Lean extern declarations found")
    declarations = {symbol: set() for symbol in symbols}
    prototype = re.compile(
        r'^((?:(?:LEAN_EXPORT|extern)\s+)*[A-Za-z_][A-Za-z_0-9 \t*]*?)'
        r'\s+([A-Za-z_][A-Za-z_0-9]*)\s*\(([^;{}]*)\)\s*;', re.MULTILINE)
    for source in sorted((root / ".lake/build/ir").rglob("*.c")):
        for match in prototype.finditer(source.read_text()):
            if match[2] in declarations:
                result = " ".join(match[1].split())
                arguments = " ".join(match[3].split()) or "void"
                declarations[match[2]].add(f"{result} {match[2]}({arguments});")
    missing = sorted(symbol for symbol, values in declarations.items() if not values)
    if missing:
        fail("no generated prototype for Lean externs: " + ", ".join(missing))
    output = root / ".lake/build/ffi"
    output.mkdir(parents=True, exist_ok=True)
    header = output / "externs.h"
    header.write_text('#include <lean/lean.h>\n' + "\n".join(
        declaration for symbol in sorted(declarations)
        for declaration in sorted(declarations[symbol])) + "\n")
    prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    compiler = shlex.split(os.environ.get("CC", "cc"))
    sources = sorted((root / "c").glob("*.c"))
    if not sources:
        fail("no C translation units found")
    definitions = {}
    references = {}
    with tempfile.TemporaryDirectory(prefix="objects-", dir=output) as temporary:
        for source in sources:
            obj = pathlib.Path(temporary) / (source.stem + ".o")
            subprocess.run(compiler + [
                "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror", "-D_GNU_SOURCE",
                "-fstack-protector-strong", "-D_FORTIFY_SOURCE=2",
                "-I", str(pathlib.Path(prefix) / "include"),
                "-include", str(header), "-c", str(source), "-o", str(obj)
            ], check=True)
            table = subprocess.check_output(
                ["nm", "-g", "--format=posix", str(obj)], text=True)
            for line in table.splitlines():
                name, kind, *_ = line.split()
                if kind in ("T", "W", "i", "I"):
                    definitions.setdefault(name, set()).add(source.name)
                elif kind in ("U", "w"):
                    references.setdefault(name, set()).add(source.name)
    missing = symbols - definitions.keys()
    runtime = pathlib.Path(prefix) / "lib/lean"
    for pattern, dynamic in (("*.so", True), ("*.a", False)):
        for library in sorted(runtime.glob(pattern)):
            if not missing:
                break
            missing -= defined_functions(library, dynamic)
    libc = pathlib.Path(subprocess.check_output(
        compiler + ["-print-file-name=libc.so.6"], text=True).strip())
    if not libc.is_file():
        fail("cannot locate libc.so.6 through the C compiler")
    interpositions = defined_functions(libc, dynamic=True)
    dead = sorted(symbol for symbol, owners in definitions.items()
                  if symbol not in symbols and symbol not in interpositions
                  and not (references.get(symbol, set()) - owners))
    errors = []
    if missing:
        errors.append("Lean externs without C or Lean runtime definitions: " + ", ".join(sorted(missing)))
    if dead:
        errors.append("C functions without Lean externs, cross-file C callers, or libc interposition: "
                      + ", ".join(dead))
    if errors:
        fail("\ncheck-ffi: ".join(errors))
    print(f"check-ffi: checked {len(symbols)} Lean externs across {len(sources)} C files; "
          "no ABI mismatches, missing definitions, or dead exports")


try:
    main()
except subprocess.CalledProcessError as error:
    sys.exit(error.returncode)
PY
