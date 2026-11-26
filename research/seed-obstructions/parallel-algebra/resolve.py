from collections import defaultdict
from functools import lru_cache
from itertools import chain
reachable=defaultdict(set)
for line in open('reachable.txt'):
 a,b=map(int,line.split());reachable[a].add(b);reachable[b].add(a)
values=list(reachable)
@lru_cache(None)
def fit(lo,hi):return tuple(f for f in values if f&lo==lo and f&hi==f)
hard=[]
for line in open('triples.txt'):
 z,a,b,u,v=map(int,line.split())
 if u in reachable[v]:continue
 sa=fit(u,a);sb=set(fit(v,b))
 if not any(reachable[h]&sb for h in sa):hard.append((z,a,b,u,v))
print(len(hard),'of',sum(1 for l in open('triples.txt')),flush=True)
with open('actual-hard.txt','w') as f:
 for row in hard: print(*row,file=f)
