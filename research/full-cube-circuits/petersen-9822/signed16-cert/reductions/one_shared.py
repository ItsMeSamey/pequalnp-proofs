from itertools import combinations
from collections import Counter
from functools import cache
from paid_order import edges,f
V=1023; H=1024
N={1<<i:sum(1<<(b if a==i else a) for a,b in edges if i in (a,b)) for i in range(10)}
def bits(m):
 while m:
  b=m&-m;yield b;m^=b
def subs(m):
 n=m
 while True:
  yield n
  if not n:return
  n=(n-1)&m
@cache
def neighbors(m):
 v=0
 for b in bits(m):v|=N[b]
 return v
@cache
def p4s(m):
 out=[]
 for a in combinations(bits(m),4):
  q=sum(a)
  if sorted((N[b]&q).bit_count() for b in a)==[1,1,2,2]:out.append(q)
 return tuple(out)
def check(S,T,U):
 act=[(b,N[b]&U) for b in bits(S) if N[b]&U]
 K=act[0][1] if act else 0; A=sum(b for b,_ in act)
 if K and (any(k!=K for b,k in act) or neighbors(S)&S or any(N[t]&S and A&~N[t] and K&~N[t] for t in bits(T))):return
 d=set()
 for t in subs(T):
  n=neighbors(t)
  if n&t:continue
  if n&S or neighbors(S)&S:
   d.update(p4s(S&~n)); d.update(p4s(U&~n))
  elif A and K&~n:d.update(p4s(U&~n))
 if any(not q&~15 for q in d):return False
 @cache
 def cover(d):
  if not d:return 0
  a=min(d,key=lambda q:(q&~15).bit_count())
  return 1+min(cover(tuple(q for q in d if not q&b)) for b in bits(a&~15))
 return T.bit_count()+cover(tuple(sorted(d)))<=5

def brute(S,T,U):
 return all(len({tuple(f[s|t|u] for u in subs(U)) for s in subs(S)})<=2 for t in subs(T))
if __name__=='__main__':
 c=Counter(); hist=Counter();controls=0
 for T in subs(V&~15):
  if T.bit_count()>5:continue
  for S in subs(V^T):
   U=V^T^S
   if (S|T).bit_count()<2:continue
   k=(not S,not U)
   z=check(S,T,U)
   if ((S*73+T*31)%197)==0:
    assert (z is not None)==brute(S,T,U);controls+=1
   c[k,'all']+=1
   if z is not None:
    c[k,'bit']+=1;hist[T.bit_count(),'bit']+=1
    if z:c[k,'priced']+=1;hist[T.bit_count(),'priced']+=1
 print('controls',controls,'counts',sorted(c.items()),'by T',sorted(hist.items()))
