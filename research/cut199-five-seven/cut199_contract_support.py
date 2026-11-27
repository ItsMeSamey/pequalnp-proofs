import json
from pathlib import Path
from itertools import combinations_with_replacement
root=Path(__file__).resolve().parent
src=json.loads((root/'cut199-contraction-quartets.json').read_text())
def support(word):return sum((word>>(1<<i)&1)<<i for i in range(5))
ors=[sum(bool(y&m)<<y for y in range(32)) for m in range(32)]
by={}
for idx,r in enumerate(src):
    for j,w in enumerate(r['w']):
        fixed=[support(t) for i,t in enumerate(r['w']) if i!=j];s=support(w)
        for a,b in combinations_with_replacement(range(32),2):
            disj=(a|b)==s
            conj=(a&b)==s and not((ors[a]&ors[b])&~w)
            if not(disj or conj):continue
            bank=tuple(sorted(fixed+[a,b]))
            if bank not in by:by[bank]=[idx,j,a,b,'and' if conj else 'or']
print(len(by),'different five-support multisets')
(root/'cut199-contract-supports.json').write_text(json.dumps([dict(s=q,source=t) for q,t in by.items()]))
