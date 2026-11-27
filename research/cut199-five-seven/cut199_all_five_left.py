"""Enumerate every compatible p=5 left code, independently of local gate budget."""
import json
from itertools import product
from pathlib import Path
from cut199_donor_modules import F
root=Path(__file__).resolve().parent
raw=[sum((x>>i&1)<<x for x in range(32)) for i in range(5)]
mon=[0,1]
for i in range(3):mon=[u|(v<<(1<<i)) for u in mon for v in mon if not u&~v]
opts=[]
for i in range(3):
    js=[j for j in range(4) if j!=i]
    family=set()
    for m in mon:
        if m&1:continue
        z=raw[i]
        for x in range(16,32):
            y=sum((x>>j&1)<<k for k,j in enumerate(js))
            z|=(m>>y&1)<<x
        family.add(z)
    opts.append(sorted(family))
p=[sum(v<<y for y,v in enumerate(row)) for row in F]
required=[(i,j) for i,a in enumerate(p) for j,b in enumerate(p) if a&~b]
def cover(z):return sum(((z>>i&1) and not(z>>j&1))<<k for k,(i,j) in enumerate(required))
c={w:cover(w) for ws in opts+[raw[3:]] for w in ws}
goal=(1<<len(required))-1
found=[]
for a,b,d in product(*opts):
    if c[a]|c[b]|c[d]|c[raw[3]]|c[raw[4]]==goal:found.append([a,b,d,raw[3],raw[4]])
(root/'cut199-all-five-left.json').write_text(json.dumps(found))
print('choices',list(map(len,opts)),'valid',len(found))
