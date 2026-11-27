#!/usr/bin/env python3
"""Check the published source, object and direct-import ledger without running Lean."""
import hashlib
import json
from pathlib import Path
from graphlib import TopologicalSorter
from collections import Counter

PACKAGE = Path(__file__).resolve().parent
EXT = {"PEqualNP.Defs","Mathlib.Combinatorics.Enumerative.DoubleCounting"}
ENDPOINT = "PEqualNP.Outside.L_meta_4186_aux.Q1Double.complete"
PROBE = "Q1DoubleCompleteAxioms"


def require(test, message):
    if not test:
        raise ValueError(message)


def main():
    manifest = json.loads((PACKAGE / "kernel-manifest.json").read_text())
    require(manifest["endpoint"] == ENDPOINT, "Wrong theorem")
    rows = {r["module"]:r for r in manifest["modules"]}
    require(len(rows) == len(manifest["modules"]), "Duplicate module entries")
    src = PACKAGE / "src"
    require(rows.keys() == {p.stem for p in src.glob("*.lean")}, "Module inventory mismatch")
    edges = {}
    seen_ext = {}
    for name, row in rows.items():
        path = src / (name+".lean")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == row["source_sha256"],
                f"Source digest mismatch: {name}")
        deps = set()
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                deps.update(line.split("--",1)[0].split()[1:])
        links = row["current_imports"]
        require(deps == set(links), f"Direct import list differs: {name}")
        require(row["staged_source_matches"] and not row["issues"] and not row["invalidated_by"],
                f"Unresolved data: {name}")
        evidence = row["evidence"]
        if evidence == "captured-at-build":
            capture = row["captured"]
            require(capture["exit"] == 0 and capture["source"] == row["source_sha256"]
                    and capture["output"] == row["olean_sha256"], f"Invalid kernel receipt: {name}")
            expected = {d:links[d]["olean_sha256"] for d in deps if d in rows}
            require(all(capture["imports"].get(d)==h for d,h in expected.items()),
                    f"Captured import mismatch: {name}")
        elif evidence == "isolated-byte-identical-replay":
            r = row["replay"]
            require(r["exit"] == 0 and r["context_unchanged"]
                    and r["source"] == row["source_sha256"]
                    and r["old"] == r["new"] == row["olean_sha256"]
                    and r["imports"] == {d:links[d]["olean_sha256"] for d in deps},
                    f"Isolated replay mismatch: {name}")
        elif evidence == "exit-zero-source-object/direct-imports-reconstructed":
            require(row["source_object_receipt"] == {"module":name,"utc":row["receipt_utc"],
                    "exit":0,"source":row["source_sha256"],"output":row["olean_sha256"]}
                    and row["object_mtime_ns"]>0,
                    f"Missing source/object receipt: {name}")
        else:
            raise ValueError(f"Unverified module {name}: {evidence}")
        for dep in deps:
            binding = links[dep]
            if dep in rows:
                target = rows[dep]
                require(binding["source_sha256"] == target["source_sha256"]
                        and binding["olean_sha256"] == target["olean_sha256"],
                        f"Dependency hash mismatch: {name} imports {dep}")
                if evidence == "exit-zero-source-object/direct-imports-reconstructed":
                    require(target["object_mtime_ns"] <= row["object_mtime_ns"],
                            f"Reconstructed import postdates consumer: {name} imports {dep}")
            else:
                require(dep in EXT and binding["source_sha256"] and binding["olean_sha256"],
                        f"Unidentified upstream dependency: {name} imports {dep}")
                require(seen_ext.setdefault(dep,binding) == binding,
                        f"Multiple upstream identities for {dep}")
        edges[name] = deps & rows.keys()
    order = tuple(TopologicalSorter(edges).static_order())
    used = set()
    def visit(n):
        if n not in used:
            used.add(n)
            for d in edges[n]:
                visit(d)
    visit(PROBE)
    require(used == set(order), "Ledger includes modules outside the endpoint/probe closure")
    require(rows[PROBE]["current_imports"].keys() == {"Q1DoubleComplete"}, "Wrong axiom probe")
    print(f"Verified {len(rows)} source/object bindings for {ENDPOINT}")
    for k,v in sorted(Counter(r["evidence"] for r in rows.values()).items()):
        print(f"{k}: {v}")


if __name__ == "__main__":
    main()
