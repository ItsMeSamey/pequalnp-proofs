from sys import path
from pathlib import Path
from itertools import combinations
from collections import Counter
base=Path(__file__).resolve().parents[1]/'one-surplus';path.insert(0,str(base))
from verify_packing import samples
rows,_,tg=samples(base/'L-meta-18968.json')
ng=[n for i,n in enumerate(rows) if not tg>>i&1];ps=[n for i,n in enumerate(rows) if tg>>i&1]
stars=[sum({n&8191 for n in ps if n>>(13+j)&1}) for j in range(7)]
hist=Counter()
for s,r in combinations([i for i in range(1,128) if i.bit_count()>=2],2):
 ok=[n for n in ng if (n>>13)&s and (n>>13)&r]
 bad=[p for p in range(13) if not any(n>>p&1 for n in ok)]
 lc=(s|r).bit_count()-1 if s&r else s.bit_count()+r.bit_count()-2
 miss=[(l,p) for l,L in enumerate(stars) for p in bad if L>>p&1]
 hist[len(bad),len(miss),lc]+=1
print('count',sum(hist.values()),'bad size dist',Counter({b:sum(v for (i,m,l),v in hist.items() if i==b) for b,m,l in hist}))
print('bad incidences',sorted(hist.items()))
