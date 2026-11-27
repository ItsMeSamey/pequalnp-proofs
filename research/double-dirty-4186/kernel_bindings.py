"""Capture the source and direct object hashes used during portable replay."""
import hashlib
import json
from pathlib import Path

def digest(path):
    sha = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            sha.update(chunk)
    return sha.hexdigest()

def snapshot(source, directories):
    imports = {}
    for line in source.read_text().splitlines():
        if not line.startswith("import "):
            continue
        for name in line.split()[1:]:
            if name.startswith("--"):
                break
            rel = Path(*name.split(".")).with_suffix(".olean")
            obj = next((base / rel for base in directories if (base / rel).is_file()), None)
            if obj is None:
                raise ValueError(f"Cannot locate {name} for the recorded Lean path")
            row = {"olean_sha256":digest(obj)}
            local = source.parent / (name+".lean")
            if local.is_file():
                row["source_sha256"] = digest(local)
            imports[name] = row
    return {"module":source.stem,"source_sha256":digest(source),"imports":imports}

def append_success(log, before, source, directories, obj, completed):
    completed.check_returncode()
    if snapshot(source,directories) != before:
        raise ValueError(f"Inputs changed while checking {source.stem}")
    row = dict(before, exit_code=completed.returncode, olean_sha256=digest(obj),
               output_sha256=hashlib.sha256(completed.stdout.encode()).hexdigest())
    with log.open("a") as file:
        print(json.dumps(row,sort_keys=True),file=file)
