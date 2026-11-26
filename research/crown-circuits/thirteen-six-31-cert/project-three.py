from collections import Counter
from pathlib import Path
import gzip,sys
P=Path(sys.argv[1]); allbits=(1<<64)-1
sides=[sum(1<<p for p in range(64) if p>>k&1) for k in range(6)]
hist=Counter()
def partition(sigs):
    groups=[allbits]
    for s in sigs:
        groups=[v for a in groups for v in (a&s,a&~s) if v]
    return groups
surv=open('projected-three.tsv','w')
for i,line in enumerate(gzip.open(P,'rt')):
    us=list(map(int,line.split()))
    bs=[x&h for j,x in enumerate(us) for h in (sides[j],allbits^sides[j])]
    atoms=partition(bs)
    if len(atoms)<13:hist['atom']+=1;continue
    events=[sum(1<<i for i,a in enumerate(atoms) if a&b) for b in bs]
    if any(e.bit_count()<3 for e in events):hist['port']+=1;continue
    def clash(pool,need):
        if not need:return True
        return any(clash([y for y in pool[i+1:] if not(x&y)],need-1) for i,x in enumerate(pool) if i+need<=len(pool))
    if clash(events,5):hist['clash']+=1;continue
    W=set(us)-set(bs)-{allbits};q=6-len(W)
    hist['survive',q]+=1
    print(i,*us,file=surv)
print(hist)
