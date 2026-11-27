#!/usr/bin/env python3
"""Verify pinned sources and compile every local module in import order."""
import argparse
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

PACKAGE = Path(__file__).resolve().parent
SOURCE = PACKAGE / "src"
ENDPOINT = "PEqualNP.Outside.L_meta_4186_aux.Q0.complete"


def check_manifest(name, root):
    checked = set()
    for line in (PACKAGE / name).read_text().splitlines():
        digest, filename = line.split(maxsplit=1)
        path = (root / filename.removeprefix("*")).resolve()
        if not path.is_relative_to(root) or path in checked:
            raise ValueError(f"Invalid manifest path: {path}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"SHA-256 mismatch: {path}")
        checked.add(path)
    if not checked:
        raise ValueError(f"Empty manifest: {name}")
    return checked


def order_sources():
    modules = {p.stem: p for p in sorted(SOURCE.glob("*.lean"))}
    graph = TopologicalSorter()
    for name, path in modules.items():
        imports = [dep for line in path.read_text().splitlines() if line.startswith("import ")
                   for dep in line.split()[1:]]
        missing = {dep for dep in imports if dep not in modules and dep != "PEqualNP.Defs"
                   and dep != "Mathlib" and not dep.startswith("Mathlib.")}
        if missing:
            raise ValueError(f"Unbundled imports in {name}: {missing}")
        graph.add(name, *(dep for dep in imports if dep in modules))
    if not {"Q0CompleteAxioms", "Q0Complete", "Graph18272Bridge"} <= modules.keys():
        raise ValueError("Missing endpoint, axiom probe or bridge")
    return list(graph.static_order())


def replay(upstream, output, order):
    project = upstream / "lean"
    subprocess.run(["lake", "build", "+PEqualNP.Defs:olean",
                    "+Mathlib.Combinatorics.Enumerative.DoubleCounting:olean"], cwd=project, check=True)
    query = "import json,os; print(json.dumps(dict(os.environ)))"
    env = json.loads(subprocess.check_output(
        ["lake", "env", sys.executable, "-c", query], cwd=project, text=True))
    entries = [str((project / p).resolve()) for p in env["LEAN_PATH"].split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([str(output), *entries])
    env["ELAN_TOOLCHAIN"] = (project / "lean-toolchain").read_text().strip()
    for name in order:
        print(f"Checking {name}", flush=True)
        result = subprocess.run(["lean", "-o", str(output / (name + ".olean")), name + ".lean"],
                                cwd=SOURCE, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        print(result.stdout, end="", flush=True)
        result.check_returncode()
        if name == "Q0CompleteAxioms":
            pattern = re.escape(ENDPOINT) + r"'? depends on axioms:\s*\[([^\]]*)\]"
            match = re.search(pattern, result.stdout)
            if not match or {a.strip() for a in match[1].split(",")} != {
                    "propext", "Classical.choice", "Quot.sound"}:
                raise ValueError("Unexpected endpoint axiom report")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="repository root containing lean/")
    parser.add_argument("--output", type=Path, help="retain objects in a new directory")
    parser.add_argument("--plan", action="store_true", help="verify sources and print order")
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    checked = check_manifest("sources.sha256", PACKAGE)
    check_manifest("upstream.sha256", upstream)
    if not set(SOURCE.glob("*.lean")) <= checked:
        raise ValueError("Unmanifested local Lean source")
    order = order_sources()
    if args.plan:
        print("\n".join(order))
    elif args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
        replay(upstream, output, order)
    else:
        with tempfile.TemporaryDirectory(prefix="lean-zero-charge-") as output:
            replay(upstream, Path(output), order)


if __name__ == "__main__":
    main()
