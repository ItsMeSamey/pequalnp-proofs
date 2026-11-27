from prefix import cliques,signal
from functools import lru_cache
from collections import Counter
ALL=255
def unions(bank):
 s={0}
 for v in bank:s|={w|v for w in s}
 return s
def splits(active,axis):
 sign=sum(1<<i for i in range(8) if i>>axis&1)
 return active&sign,active&(ALL^sign)
def banks(bank,axis):
 if axis==3:
  yield bank;return
 for u in sorted((unions(bank)|{ALL})-{0}):
  yield from banks(bank+splits(u,axis),axis+1)
def hot(v):return int(signal(v,1))+2*int(signal(v,2))
def combine(s):
 m=0
 for v in s:m|=hot(v)
 return m
trans={t:{(len(s),combine(s)) for s in cliques(t)} for t in range(4)}
@lru_cache(None)
def possible(h):
 options={(0,0)}
 for t,n in enumerate(h):
  for _ in range(n):options={(i+j,x|y) for i,x in options for j,y in trans[t] if i+j<=14}
 return {x for n,x in options if n==14}

from itertools import combinations
def facecap(t,op,pol):
 def f(v):
  x,y,k,j=[bool(v>>i&1) for i in range(4)]
  d=x and y if op else (x,y)[pol]
  b=k and (d or j) if not op else (k,d or j)[pol]
  return (t&1 and d) or (t&2 and b)
 cold=[v for v in range(16) if not f(v)]
 return max(n for n in range(5) if any(all(f(v|w) for v,w in combinations(c,2)) for c in combinations(cold,n)))
C={(t,o,p):facecap(t,o,p) for t in range(4) for o in range(2) for p in range(2)}
counts=Counter()
for bank in banks((),0):
 tr={i:tuple(v>>i&1 for v in bank) for i in range(8)}
 for d in unions(bank):
  for b in unions(bank):
   obs={tr[i]:(d>>i&1)+2*(b>>i&1) for i in range(8)}
   h=tuple(list(obs.values()).count(k) for k in range(4))
   if h!=(2,0,4,0) or 3 not in possible(h):continue
   counts['input']+=1
   caps=[sum(obs[x]+1 for x in {tr[i] for i in range(8) if (i>>a&1)==p}) for a in range(3) for p in range(2)]
   early=[sum(C[t,o,p] for t in obs.values()) for o in range(2) for p in range(2)]
   active=next(bank[2*a]|bank[2*a+1] for a in range(3) if (bank[2*a]|bank[2*a+1])!=255)
   H=next(a for a in range(3) if (bank[2*a]|bank[2*a+1])==255 and active not in bank[2*a:2*a+2])
   cat='rows' if all((b>>i&1)==(b>>(i^(1<<H))&1) for i in range(8)) else 'column'
   counts[cat]+=1
   counts[cat+'_new']+=min(caps+early)>=4
   if min(caps[:2])<4:counts['last']+=1
   if min(caps)<4:counts['any_tail']+=1
   if min(caps+early)<4:counts['any_of_five']+=1
print('caps',C,'counts',counts)
