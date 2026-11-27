"""Physical fork lower-bound histogram for all 32767 flag bipartitions."""
from collections import Counter
from pathlib import Path
import runpy
rows=runpy.run_path(str(Path(__file__).parent/'fano20-canonical'/'encode.py'))['cases']()
edges=[tuple(j for j in range(12) if m>>j&1) for m,p in sorted(rows) if p]
def lower(mask):
    chosen=[e for i,e in enumerate(edges) if mask>>i&1]
    degree=[0]*12
    for a,b in chosen: degree[a]+=1;degree[b]+=1
    adj=[[] for i in range(6)]
    for a,b in chosen:
        if min(degree[a],degree[b])>=2:adj[a].append(b)
    owner={}
    def augment(a,seen):
        for b in adj[a]:
            if b in seen:continue
            seen.add(b)
            if b not in owner or augment(owner[b],seen):
                owner[b]=a
                return True
        return False
    return sum(bool(d) for d in degree)-1+sum(augment(a,set()) for a in range(6))
hist=Counter()
for mask in range(1,1<<15):hist[1+lower(mask)+lower(65535^mask)]+=1
print(sorted(hist.items()))
