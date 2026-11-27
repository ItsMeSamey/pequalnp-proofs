#!/usr/bin/env python3
"""Audit and recheck the exact-seven lower bound without previous certificate objects."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess

here = Path(__file__).resolve().parent
src = here / "src"
modules = {".".join(p.relative_to(src).with_suffix("").parts): p for p in src.rglob("*.lean")}
order, visiting, done = [], set(), set()
external = {"Std", "PEqualNP.Defs"}

def visit(name):
    if name in done:
        return
    if name in visiting:
        raise ValueError(f"cyclic import at {name}")
    visiting.add(name)
    for entry in re.findall(r"^import\s+([\w.]+)\s*$", modules[name].read_text(), re.M):
        if entry in modules:
            visit(entry)
        elif entry not in external:
            raise ValueError(f"unbundled dependency of {name}: {entry}")
    visiting.remove(name)
    done.add(name)
    order.append(name)

def checkpoint():
    for line in (here / "SHA256SUMS").read_text().splitlines():
        expected, filename = line.split("  ", 1)
        if hashlib.sha256((here / filename).read_bytes()).hexdigest() != expected:
            raise ValueError(f"checksum mismatch: {filename}")
    visit("Axioms23724")
    visit("Control23724")
    if done != set(modules):
        raise ValueError(f"unreachable modules: {set(modules)-done}")
    print(f"All {len(order)} bundled modules reachable, external imports: {sorted(external)}", flush=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit-only", action="store_true")
    ap.add_argument("--lean-project", type=Path, help="Pinned pequalnp-proofs lean directory")
    ap.add_argument("--build-dir", type=Path, help="Fresh output directory")
    args = ap.parse_args()
    checkpoint()
    if args.audit_only:
        raise SystemExit(0)
    if args.lean_project is None or args.build_dir is None:
        ap.error("provide --lean-project and --build-dir to compile")
    project, build = args.lean_project.resolve(), args.build_dir.resolve()
    if (project/"lean-toolchain").read_text().strip() != "leanprover/lean4:v4.36.0":
        raise ValueError("toolchain differs from Lean v4.36.0")
    build.mkdir(parents=True, exist_ok=True)
    if any(build.iterdir()):
        raise ValueError("choose a fresh, empty build directory")
    env = dict(os.environ)
    env.pop("LEAN_PATH",None)
    paths = subprocess.check_output(["lake","env","printenv","LEAN_PATH"],cwd=project,env=env,text=True).strip()
    compiler = subprocess.check_output(["lake","env","which","lean"],cwd=project,env=env,text=True).strip()
    env["LEAN_PATH"] = str(build) + os.pathsep + paths
    for number,name in enumerate(order,1):
        path=modules[name]
        target=(build / path.relative_to(src)).with_suffix(".olean")
        target.parent.mkdir(parents=True,exist_ok=True)
        print(f"{number}/{len(order)} {name}",flush=True)
        result=subprocess.run([compiler,"-j1",f"--root={src}","-o",str(target),str(path)],
            cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        log=(build / (name+".log"))
        log.write_text(result.stdout)
        if result.returncode:
            raise SystemExit(result.stdout or f"Lean exited {result.returncode} at {name}")
    receipt=(build / "Axioms23724.log").read_text()
    if receipt != (here/"receipts/Axioms23724.log").read_text():
        raise SystemExit("endpoint axiom report differs from the frozen receipt")
    print(receipt,end="")
