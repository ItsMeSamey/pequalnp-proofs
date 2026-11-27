"""Replay a snapshot in a separate directory, in the assigned single-compiler slot."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

source = Path(__file__).resolve().parent
manifest = json.loads((source / "run-pin-manifest.json").read_text())


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check(path, expected):
    if not path.is_file() or digest(path) != expected:
        raise SystemExit(f"Missing or changed artifact: {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("verify", "prepare", "compile"))
    parser.add_argument("destination", nargs="?", type=Path)
    parser.add_argument("--start", type=int, default=1, help="First module, one-based")
    parser.add_argument("--count", type=int, help="Number of modules in this serial batch")
    args = parser.parse_args()
    modules = manifest["modules"]
    if args.mode == "verify":
        for path, expected in manifest["files"].items():
            check(source / path, expected)
        print(f"Verified {len(modules)} modules and {len(manifest['files'])} files.")
        return
    if args.destination is None:
        parser.error("provide a fresh replay directory")
    dest = args.destination.resolve()
    if dest == source or source in dest.parents:
        parser.error("use a directory outside the frozen snapshot")
    inputs = ["guarded_compile.py"] + [module["name"] + ".lean" for module in modules]
    if args.mode == "prepare":
        dest.mkdir(exist_ok=False, parents=True)
        for name in inputs:
            check(source / name, manifest["files"][name])
            shutil.copyfile(source / name, dest / name)
        (dest / "objects").mkdir()
        (dest / "receipts").mkdir()
        print(dest)
        return
    if args.start < 1 or args.start > len(modules) or (args.count is not None and args.count < 1):
        parser.error("invalid replay batch")
    selected = modules[args.start - 1:][:args.count]
    for name in inputs:
        check(dest / name, manifest["files"][name])
    if not os.environ.get("LEAN_CGROUP_NONRECLAIMABLE_LIMIT"):
        parser.error("use the assigned compiler lane's nonreclaimable memory limit")
    for module in selected:
        for dep in module["internal_imports"]:
            if not (dest / "objects" / (dep + ".olean")).is_file():
                raise SystemExit(f"Missing fresh prerequisite for {module['name']}: {dep}")
        subprocess.run([sys.executable, str(dest / "guarded_compile.py"), module["name"]],
                       check=True, cwd=dest)
        obj = dest / "objects" / (module["name"] + ".olean")
        if digest(obj) != manifest["files"]["objects/" + obj.name]:
            raise SystemExit(f"Independent object differs from first pass: {obj}")


if __name__ == "__main__":
    main()
