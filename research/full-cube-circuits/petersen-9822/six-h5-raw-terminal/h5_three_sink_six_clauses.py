from itertools import combinations_with_replacement
from pathlib import Path
from h5_raw_terminal import EDGES,target
N=[x for x in range(1024) if not target(x) and all(target(x|1<<i) for i in range(10) if not x>>i&1)]
def tr(x,S):return sum(1<<i for i,s in enumerate(S) if x&s)
r=[(tr(x,EDGES),tr(x,N)) for x in range(1024)]
for line in (Path(__file__).parent/'h5-pairing-exceptions.tsv').open():
 rank,a,b=map(int,line.split())
 if rank<5:continue
 h=(r[a][0]&r[b][0],r[a][1]&r[b][1]);bank=set(r+[(p|h[0],n|h[1]) for p,n in r])
 qs={(p&q,n&m) for (p,n),(q,m) in combinations_with_replacement(bank,2) if p&q and 0<(n&m).bit_count()<=2*(rank-4)}
 cover0={65535^n for p,n in bank if p==8191}
 good=[]
 for qp,qn in qs:
  sets=cover0|{65535^(n|qn) for p,n in bank if p|qp==8191}
  opts=[[s for s in sets if s>>i&1] for i in range(16)]
  def attainable(m,k):
   if not m:return True
   if not k:return False
   choices=min((opts[i] for i in range(16) if m>>i&1),key=len)
   return any(attainable(m&~s,k-1) for s in choices if (m&~s).bit_count()<=4*(k-1))
  if attainable(65535,6):good.append((qp,qn))
 assert not good
 print(rank,a,b,len(qs),len(good),flush=True)
