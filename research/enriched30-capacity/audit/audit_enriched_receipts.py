"""Audit staged Lean modules against historical steward and launch receipts, without compiling."""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import re

ROOTS = ("Enriched30ActualCostAxioms", "EnrichedCapacityAxioms", "Enriched30UnanchoredCostAxioms")
HEX = r"[0-9a-f]{64}"
IMPORT = re.compile(r"^import\s+([\w.]+)\s*$", re.MULTILINE)


def digest(path):
    return sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def compare(expected, actual):
    if actual is None or expected is None:
        return "unmatched"
    return "matched" if expected == actual else "mismatched"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, default=Path(__file__).with_name("enriched30-capacity-release"))
    parser.add_argument("--objects", type=Path, default=Path("/dev/shm/official-20579-imports"))
    parser.add_argument("--ledger", type=Path, default=Path("/tmp/formal-kernel-success.tsv"))
    parser.add_argument("--launch-dir", type=Path, default=Path("/tmp"))
    args = parser.parse_args()
    manifest = json.loads((args.stage / "IMPORTS.json").read_text())
    queue = list(ROOTS)
    rows = {}
    problems = []
    receipts = defaultdict(list)
    if args.ledger.is_file():
        for number, line in enumerate(args.ledger.read_text().splitlines(), 1):
            if not line.strip():
                continue
            fields = line.split()
            if len(fields) != 4 or not all(re.fullmatch(HEX, value) for value in fields[2:]):
                problems.append(f"malformed ledger entry at line {number}")
                continue
            date, module, source, obj = fields
            receipts[module].append((date, number, source, obj))
    else:
        problems.append("ledger unavailable")
    while queue:
        module = queue.pop()
        if module in rows or module == "Mathlib" or module.startswith("Mathlib."):
            continue
        relative = Path(*module.split("."))
        source = args.stage / relative.with_suffix(".lean")
        obj = args.objects / relative.with_suffix(".olean")
        src_hash, obj_hash = digest(source), digest(obj)
        entry = manifest.get(module, {})
        if src_hash:
            children = IMPORT.findall(source.read_text())
            if children != entry.get("inputs"):
                problems.append(f"{module}: staged imports differ from manifest")
            queue.extend(children)
        else:
            queue.extend(entry.get("inputs", []))
        row = {"source_sha256": src_hash, "object_sha256": obj_hash,
               "staged_manifest": compare(entry.get("sha256"), src_hash), "ledger": [], "launch": []}
        for date, number, recorded_source, recorded_obj in receipts[module]:
            row["ledger"].append({"date": date, "line": number, "source_recorded": recorded_source,
                                  "object_recorded": recorded_obj, "source": compare(recorded_source, src_hash),
                                  "object": compare(recorded_obj, obj_hash)})
        launch = args.launch_dir / f"launch-{module}.log"
        if launch.is_file():
            pattern = re.compile(rf"^({HEX})\s+\*?(?:\S*/)?{re.escape(relative.name)}\.lean\s*$")
            for number, line in enumerate(launch.read_text(errors="replace").splitlines(), 1):
                match = pattern.fullmatch(line)
                if match:
                    row["launch"].append({"line": number, "source_recorded": match[1],
                                          "source": compare(match[1], src_hash)})
        # Launch output records a source hash only. A current artifact or an empty
        # compile log cannot recover a historical object hash or an exit status.
        if any(r["source"] == r["object"] == "matched" for r in row["ledger"]):
            row["pair_status"] = "matched"
        elif any("mismatched" in (r["source"], r["object"]) for r in row["ledger"]):
            row["pair_status"] = "mismatched"
        else:
            row["pair_status"] = "unmatched"
        rows[module] = row
    counts = Counter(row["pair_status"] for row in rows.values())
    summary = {"root_modules": ROOTS, "ledger": str(args.ledger), "object_root": str(args.objects),
               "pair_counts": counts, "problems": problems, "modules": dict(sorted(rows.items()))}
    print(json.dumps(summary, indent=2) )
    mismatches = any(row["staged_manifest"] == "mismatched" or
                     any("mismatched" in (r["source"], r["object"]) for r in row["ledger"]) or
                     any(r["source"] == "mismatched" for r in row["launch"]) for row in rows.values())
    if mismatches or problems:
        return 1
    return 2 if counts["unmatched"] or any(row["staged_manifest"] == "unmatched" for row in rows.values()) else 0


if __name__ == "__main__":
    raise SystemExit(main())
