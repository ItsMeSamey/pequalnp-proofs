from itertools import combinations
n=5
F=2**32-1
edges=[1<<i|1<<((i+1)%n) for i in range(n)]
T=sum(1<<x for x in range(32) if any(x&e==e for e in edges))
B=frozenset(sum(1<<x for x in range(32) if x&m==m) for m in range(32))
perms=[[sum(1<<((s*k+j)%n) for k in range(n) if x>>k&1) for x in range(32)] for s in (-1,1) for j in range(n)]
def canon(h):return all(h<=sum(1<<p[x] for x in range(32) if h>>x&1) for p in perms)
def new(b):return ({x^F for x in b}|{x|y for x,y in combinations(b,2)})-b
def extend(b,h):return b|{h&x for x in b}
def last(b,t):
 g=F
 for x in b:
  if x&t==t:g&=x
 if g==t or any((x^F)&g==t for x in b):return True
 c=[x for x in b if not(x&g&~t)]
 return any((x|y)&t==t for x,y in combinations(c,2))
assert last(B,F^next(x for x in B if x.bit_count()==16))
assert all(bool((T>>x)&1)==bool(((x&1) and (x&18)) or ((x&4) and (x&10)) or ((x&24)==24)) for x in range(32))
ct=0
for h in new(B):
 if not canon(h):continue
 b=extend(B,h)
 assert not last(b,T)
 for y in new(b):
  ct+=1
  if last(extend(b,y),T):raise Exception(('hit',h,y))
print('excluded',ct,flush=True)
