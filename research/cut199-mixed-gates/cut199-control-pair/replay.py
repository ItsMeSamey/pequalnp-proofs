"""Recompute structural ledgers and full-cube statistics for both controls."""
from pathlib import Path
import json
import sys
from check4186 import check
D = Path(__file__).resolve().parent
scores = {}
for name in ("raw","normalized"):
    circuit = json.loads((D / (name + ".json")).read_text())
    gates = [("and" if b else "or",a,c) for b,a,c in circuit["gates"]]
    output = circuit["output"]
    r = check(11,circuit["edges"],gates,output)
    gate_ids = set(range(len(gates)))
    clean = set(r["tops"])
    violations = [(a,j) for j,(op,_,_) in enumerate(gates) if op=="and"
                  for a in sorted(clean.intersection(r["inCone"][j]))]
    left = {0,1,2,6,7}
    supports = [{i} for i in range(11)]
    for _,a,b in gates:
        supports.append(supports[a] | supports[b])
    uses = {output}
    for j in reversed(range(len(gates))):
        if 11+j in uses:
            uses.update(gates[j][1:])
    r.update(size=len(gates), assignmentCount=2048, mismatchCount=0 if r["computes"] else None,
             liveGateCount=sum(11+i in uses for i in gate_ids),
             cleanAndAncestorsOfAnd=violations,
             cutPureLeft=sum(s<=left for s in supports[11:]),
             cutPureRight=sum(s.isdisjoint(left) for s in supports[11:]),
             cutMixed=sum(bool(s&left) and bool(s-left) for s in supports[11:]),
             qUnchargedOr=len(set(r["orN"])-set(r["lam"])),
             Q=r["rhs"], U=len(r["Ustar"]), tauPlusUMinusQ=r["lhs"]-r["rhs"])
    assert r["computes"] and r["noFourCycle"] and r["size"]==r["liveGateCount"]==22
    scores[name]=r
assert (scores["raw"]["topForm"],scores["raw"]["lhs"],scores["raw"]["rhs"])==(False,11,12)
assert (scores["normalized"]["topForm"],scores["normalized"]["lhs"],scores["normalized"]["rhs"])==(True,11,11)
serialized=json.dumps(scores,indent=2)+"\n"
if "--write" in sys.argv:
    (D/"scores.json").write_text(serialized)
else:
    assert (D/"scores.json").read_text()==serialized
for name,r in scores.items():
    print(name,{k:r[k] for k in ("size","topForm","lhs","rhs","U","qUnchargedOr","cutPureLeft","cutPureRight","cutMixed","cleanAndAncestorsOfAnd")})
