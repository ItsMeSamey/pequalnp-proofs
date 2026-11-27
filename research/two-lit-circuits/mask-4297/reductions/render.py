"""Validate a gate list on all 25 ordered probes, then render its standalone Lean proof."""
import argparse
import json
from pathlib import Path

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument("netlist", type=Path)
parser.add_argument("--control", action="store_true")
args = parser.parse_args()
budget = 7 if args.control else 6
name = "Control23724" if args.control else "L_meta_23724"
spec = (root / "statement.txt").read_text().strip()
if args.control:
    spec = spec.replace("C.size ≤ 6","C.size ≤ 7")
gates = json.loads(args.netlist.read_text())
if not isinstance(gates, list) or len(gates) > budget or not gates:
    raise ValueError("gate budget or output is invalid")
decls = []
for n,g in enumerate(gates):
    op,*ins = g
    if op not in ('and','or','not') or len(ins) != (1 if op=='not' else 2):
        raise ValueError(g)
    if any(type(w) is not int or not 0 <= w < 5+n for w in ins):
        raise ValueError(g)
    decls.append(f"⟨.{op}, {ins}⟩")
for i in range(5):
    for j in range(5):
        w=[k in (i,j) for k in range(5)]
        for op,*ins in gates:
            a=w[ins[0]]
            w.append(not a if op=='not' else (a and w[ins[1]]) if op=='and' else a or w[ins[1]])
        if w[-1] != bool((4297 >> (5*min(i,j)+max(i,j))) & 1):
            raise ValueError(f"mismatch on ordered probe {(i,j)}")
body=",\n  ".join(decls)
ns=f"PEqualNP.Outside.{name}"
(root/f"{name}.lean").write_text(f"""import PEqualNP.Defs

namespace {ns}
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  {body}], {4+len(gates)}⟩

end {ns}

theorem {ns} : {spec} := by
  refine ⟨{ns}.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, {ns}.witness]
  · decide
  · decide
""")
print(f"Verified all 25 ordered probes ({len(gates)} gates), wrote {name}.lean.")
