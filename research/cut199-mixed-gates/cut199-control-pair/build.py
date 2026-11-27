"""Extract the clean edge 5–9 and aggregate six terms in a balanced binary tree."""
import json
from pathlib import Path
D = Path(__file__).resolve().parent
raw = json.loads((D / "raw.json").read_text())
old = raw["gates"]
assert old[4] == [True, 5, 9] and old[5] == [False, 8, 15]
assert old[18:] == [[False,22,24],[False,29,25],[False,30,27],[False,31,28]]
new = []
wire = {i:i for i in range(11)}
for i, (op,a,b) in enumerate(old[:18],11):
    if i == 16:
        wire[i] = 8
    else:
        wire[i] = 11 + len(new)
        new.append([op,wire[a],wire[b]])
roots = [wire[v] for v in (22,24,25,27,28,15)]
while len(roots) > 1:
    next_level = []
    for i in range(0,len(roots)-1,2):
        next_level.append(11+len(new))
        new.append([False,roots[i],roots[i+1]])
    if len(roots) % 2:
        next_level.append(roots[-1])
    roots = next_level
assert len(new) == 22
result = dict(edges=raw["edges"],gates=new,output=roots[0])
(D / "normalized.json").write_text(json.dumps(result,indent=2)+"\n")
