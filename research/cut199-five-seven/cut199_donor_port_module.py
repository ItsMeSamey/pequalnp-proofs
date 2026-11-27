"""Necessary monotone unary-donor obligations for any fixed physical left bank."""
import json
from pathlib import Path
from itertools import combinations
from cut199_donor_modules import F
root=Path(__file__).resolve().parent
raw=[sum((x>>i&1)<<x for x in range(32)) for i in range(5)]
banks=[raw]+[[v if i==j else u for i,u in enumerate(raw)] for j,v in [(0,-84235606),(0,-5592406),(1,-3355444),(2,-986896)]]
def classify(bank,mask):
    inner=[j for j in range(5) if mask>>j&1]
    codes=[sum((w>>x&1)<<j for j,w in enumerate(bank)) for x in range(32)]
    project=lambda code:sum((code>>j&1)<<i for i,j in enumerate(inner))
    outside={}
    for x,c in enumerate(codes):outside.setdefault(c&~mask,[]).append(x)
    pos=set();neg=set();dim=len(inner)+6
    for y in range(64):
        for group in outside.values():
            vals={F[x][y] for x in group}
            if len(vals)<2:continue
            for x in group:
                k=project(codes[x])|(y<<len(inner))
                (pos if F[x][y] else neg).add(k)
    up=pos.copy()
    for j in range(dim):up|={v|1<<j for v in up}
    if up&neg:return False
    down=neg.copy()
    for j in range(dim):down|={v&~(1<<j) for v in down}
    for u,v in combinations(range(len(inner)),2):
        seen=set();a,b=1<<u,1<<v
        for k in range(1<<dim):
            if k&(a|b):continue
            corners=[k,k|a,k|b,k|a|b]
            if all(x in up or x in down for x in corners):
                word=sum((x in up)<<j for j,x in enumerate(corners))
                if word in (8,14):seen.add(word)
                if len(seen)==2:return False
    return True
result=[]
for bank in banks:
    # high 0,1,2 background freezes all early physical ports, leaves only raw6,7.
    assert all([v>>x&1 for v in bank]==[1,1,1,x>>3&1,x>>4&1] for x in [7,15,23,31])
    good=[s for s in range(1,32) if ((s>>3)&3) in (1,2) and classify(bank,s)]
    result.append(dict(bank=bank,admissible=good))
print(result)
(root/'cut199-donor-port-modules.json').write_text(json.dumps(result))
