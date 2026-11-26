from itertools import combinations,permutations
from pathlib import Path
import sys
source=Path(sys.argv[1]).resolve()
dest=Path(sys.argv[2]);dest.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(source))
from verify_packing import samples
rows,front,target=samples(source/'L-meta-18968.json')
N={(r&8191,(r>>13)&127) for i,r in enumerate(rows) if not target>>i&1}
P={(r&8191,(r>>13)&127) for i,r in enumerate(rows) if (target^front)>>i&1}
S=[sum({p for p,l in P if l>>t&1}) for t in range(7)]
for tri in combinations(range(7),3):
    union=S[tri[0]]|S[tri[1]]|S[tri[2]]
    pts=[p for p in range(13) if union>>p&1]
    out=[p for p in range(13) if not union>>p&1]
    def proj(q,which):return sum(((q>>p)&1)<<j for j,p in enumerate(which))
    rel={}
    for q,l in N:
        if not all(q&S[k] for k in range(7) if k not in tri):continue
        for t in tri:
            if l>>t&1:
                for i,p in enumerate(pts):
                    if S[t]>>p&1:
                        key=(i,proj(q,pts))
                        rel[key]=rel.get(key,0)|proj(q,out)
    strong=[(i,m) for i,m in rel if not any(i==j and m!=r and not m&~r for j,r in rel)]
    name=''.join(map(str,tri))
    with (dest/name).open('w') as f:
        print(len(pts),len(out),len(strong),len(rel),file=f)
        print(*(proj(S[t],pts) for t in tri),file=f)
        for i,m in strong: print(i,m,file=f)
        for (i,m),o in rel.items(): print(i,m,o,file=f)
