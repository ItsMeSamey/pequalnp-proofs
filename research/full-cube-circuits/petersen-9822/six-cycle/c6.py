from itertools import combinations
from functools import cache
edges=[1<<i|1<<((i+1)%6) for i in range(6)]
ind=[x for x in range(64) if not any(x&e==e for e in edges)]
ts=edges+[x for x in ind if not any(x!=y and x&y==x for y in ind)]
assert len(ts)==11
P=63; F=2047
def dom(a,b):return (b&P&~a)==0 and (a&~P&~b)==0
def prune(v):return tuple(sorted(x for x in v if not any(x!=y and dom(y,x) for y in v)))
base=prune({sum(1<<j for j,v in enumerate(ts) if v&m==m) for m in range(64)})
def ctl(x):
 a=[(x>>i)&1 for i in range(6)]
 return any(a[i] and (a[(i+1)%6] or a[(i-1)%6]) for i in [0,2,4])
assert all(ctl(x)==(x not in ind) for x in range(64))
@cache
def work(b,k):
 if P in b:return ()
 if not k:return
 keep=F
 for x in b:
  if x&P==P:keep&=x
 opts={x|y for x,y in combinations(b,2)}
 for h in opts:
  if h&keep==P:return (h,)
 if k==1:return
 for h in sorted(opts):
  if any(dom(x,h) for x in b):continue
  v=prune(set(b)|{h&x for x in b}|{h})
  t=work(v,k-1)
  if t is not None:return (h,)+t
for k in (3,4):
 print(k,work(base,k),work.cache_info(),flush=True)
