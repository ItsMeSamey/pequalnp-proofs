from minors import dataset,DEGREE_ONE
from itertools import combinations
from functools import cache
from collections import Counter
import sys
def bm(m):return [1<<i for i in range(m.bit_length())if m>>i&1]
def subs(seq,n):
 for k in range(n+1):yield from combinations(seq,k)
A=[3<<j for j in range(6)]
B=[1<<(j+3)|1<<((j+9)%13) for j in range(6)]
extra=dict(zip(A+B+[a|b for a,b in zip(A,B)],range(20,38)))
def load(e):
 d=dataset(e);W=d['original_wire_ids']
 dec=lambda r:sum(1<<w for k,w in enumerate(W)if r>>k&1)
 P=list(map(dec,d['positives']));N=list(map(dec,d['maximal_negatives']))
 return P,N
def banks(e,P,N):
 pts=8191^sum(e);lib=[0,*bm(8191),*extra]
 opt=[m for m in sorted(extra)if not any(q!=m and not q&~m and not(m&~q&pts)for q in lib)]
 for R in ([pts,pts^2]if pts&2 else [pts]):
  mandatory=R|(127<<13)
  clauses={p&~n for p in P for n in N if not (p&~n)&mandatory}
  for C in subs(opt,15-R.bit_count()):
   m=R|sum(1<<extra[c]for c in C)|127<<13
   if all(d&m for d in clauses):yield R,C
@cache
def price(K,V,s,S):
 for drop in subs(bm(K),s):
  D=sum(drop)
  if sum(max(0,(K&~D&t).bit_count()-2)for u,t in enumerate(S)if V>>u&1)<=s-len(drop):return False
 return True
def test(P,N,R,C):
 s=16-R.bit_count()-len(C);m=R|sum(1<<extra[q]for q in C)
 pos={r&8191:r&m for r in P};inc={p:sum(1<<u for u in range(7)if any(r&8191==p and r>>(13+u)&1 for r in P))for p in pos}
 S=tuple(sum(p for p,v in inc.items()if v>>u&1)for u in range(7))
 def pack(f):return sum(1<<i for i,n in enumerate(N)if f(n))
 alln=(1<<len(N))-1
 on=[pack(lambda n:n>>(13+u)&1)for u in range(7)]
 @cache
 def line(w):
  a=0
  for u in range(7):
   if w>>u&1:a|=on[u]
  return a
 meet=[pack(lambda n:any(not x&~n and p&S[u]for p,x in pos.items()))for u in range(7)]
 raw={p:pack(lambda n:n&p) for p in bm(R)}
 F={p:pack(lambda n:not n&p and not(pos[p]&~p)&~n and n>>13&inc[p])for p in raw}
 cp={q:pack(lambda n:n>>extra[q]&1)for q in C}
 for H in sorted(subs(C,len(C)),key=len,reverse=True):
  h=alln;lo=sum(1<<extra[q]for q in C if q not in H)
  for q in H:h&=cp[q]
  av=sum(1<<u for u in range(7)if all(h&on[u]&meet[v]for v in range(7)if v!=u))
  a=[p for p in raw if not lo&pos[p] and all(h&raw[p]&n for n in meet)]
  vm={p:sum(1<<u for u in range(7)if on[u]&h&F[p])for p in a}
  for U in [127,*[127^(1<<u)for u in range(7)]]:
   rows=[p for p in a if inc[p]&U not in (0,U) and all(h&raw[p]&on[u]for u in range(7)if U>>u&1 and not inc[p]>>u&1)]
   good={p:vm[p]&sum(1<<u for u in range(7)if h&on[u]&line(inc[p]&U))for p in rows}
   bad=[(p,q)for p,q in combinations(rows,2)if inc[p]&U==inc[q]&U or not h&line(inc[p]&U)&line(inc[q]&U)or not h&(F[p]&raw[q]|F[q]&raw[p])]
   for omit in subs(bm(U&av),2):
    V=(U&av)^sum(omit)
    K=sum(p for p in rows if inc[p]&V and not V&~good[p])
    def walk(k):
     if not price(k,V,s,S):return 0
     for p,q in bad:
      if k&p and k&q:return walk(k^p)or walk(k^q)
     return k
    k=walk(K)
    if k:return H,U,V,k
if __name__=='__main__':
 j=int(sys.argv[1]);e=list(combinations(DEGREE_ONE,2))[j];P,N=load(e)
 for R,C in banks(e,P,N):print((R,C,test(P,N,R,C)),flush=True)
