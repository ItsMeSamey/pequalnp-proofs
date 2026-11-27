from itertools import combinations_with_replacement
from h5_raw_terminal import EDGES,target
N=[x for x in range(1024) if not target(x) and all(target(x|1<<i) for i in range(10) if not x>>i&1)]
def tr(x,S):return sum(1<<i for i,s in enumerate(S) if x&s)
r=[(tr(x,EDGES),tr(x,N)) for x in range(1024)]
h=(r[68][0]&r[130][0],r[68][1]&r[130][1])
bank=set(r+[(p|h[0],n|h[1]) for p,n in r])
reject={65535^n for p,n in bank if p==8191}
parts={x|y for x in reject for y in reject}
from collections import defaultdict
groups=defaultdict(set)
for (p,m),(q,n) in combinations_with_replacement(bank,2):
 leak=m&n;pos=p&q
 if leak and leak.bit_count()<=4 and pos:groups[leak].add(pos)
survivors=[]
for P in parts:
 needs=8191
 for p,n in bank:
  if not n&~P:needs &=~p
 grants={p&needs for n,group in groups.items() if not n&~P for p in group}
 maximal=[p for p in grants if not any(p!=q and not(p&~q) for q in grants)]
 cover={0}
 for _ in range(3):cover|={z|p for z in cover for p in maximal}
 if needs in cover:survivors.append(P)
print(h,len(bank),len(reject),len(parts),len(survivors),survivors)

assert (len(reject),len(parts),len(survivors))==(23,236,0)
