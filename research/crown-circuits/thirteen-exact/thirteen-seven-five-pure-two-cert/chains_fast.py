from pathlib import Path
from itertools import combinations
from functools import lru_cache
import sys
def check(r,cap=1000000):
 rid,q,d,*a=r;I=a[:13];P=a[22:25];assert d==0 and not(q&3)
 rem=[2-i.bit_count() for i in I];history=[0]*13;arms=[];stats=[0,0];B=[sum(((m>>j)&1)<<i for i,m in enumerate(I)) for j in range(2)]
 Us=[sum(((m>>(j+3))&1)<<i for i,m in enumerate(I)) for j in range(3)]
 def quick(A):
  sig=[0]*13
  for j,(a,b) in enumerate(arms):
   bb=B[j//2];group=7<<(3*j)
   for i in A:
    if bb>>i&1:sig[i]|=group
    elif i==a:sig[i]|=3<<(3*j)
    elif i==b:sig[i]|=5<<(3*j)
  if len({sig[i] for i in A})<len(A):return False
  for a,b in combinations(A,2):
   z=sig[a]|sig[b]
   if not z:return False
   dom=0
   for i in A:
    if not(z&~sig[i]):dom|=1<<i
   if dom and not any(((I[a]|I[b])>>(3+j)&1) and not(dom&(Us[j]|(8191^P[j]))) for j in range(3)):return False
  return True
 def judge():
  stats[0]+=1
  if stats[0]>cap:return True
  A=[i for i,n in enumerate(rem) if not n];
  if not quick(A):return False
  sing=[1<<i for i in A];pairs=[(1<<u)|(1<<v) for u,v in combinations(A,2)];tests=sing+pairs
  f=(1<<len(tests))-1;neg=(1<<len(sing))-1;pos=f^neg
  def tt(m):return sum(bool(v&m)<<j for j,v in enumerate(tests))
  roots=[B[j//2] for j in range(4)]
  full=tuple(tt(b|(1<<u)|(1<<v)) for b,(u,v) in zip(roots,arms))
  # Overgrant either orientation for a partial first-injection tap.
  optional=list(set(tt(b|(1<<i)) for b,arm in zip(roots,arms) for i in arm)-set(full))
  e=sum(rem);U=[tt(v) for v in Us]
  bad=[neg&(u|tt(8191^p)) for u,p in zip(U,P)]+[neg]
  # Only an upper bound on the possible P-support need be checked on each untouched singleton.
  def cover(opts,want):
   if not want:return True
   if not opts:return False
   if any(all(not(x&want&(1<<i)) for z in opts for x in z) for i in range(len(tests)) if want>>i&1):return False
   return any(cover(opts[1:],want&~m) for m in opts[0])
  def passes(features,exact):
   bank=set()
   for m in features:bank|={m}|{x&m for x in bank}
   opts=[]
   for j in range(4):
    factors={x&(U[j] if j<3 else f)&pos for x in bank if not(x&bad[j])}
    if not factors:return False
    maximal=[x for x in factors if not any(x!=y and not(x&~y) for y in factors)]
    opts.append(maximal)
   if not exact:
    acc=0
    for z in opts:
     for x in z:acc|=x
    return acc==pos
   return cover(sorted(opts,key=len),pos)
  if not passes((*full,*optional),False):return False
  stats[1]+=1
  for extra in combinations(optional,min(e,len(optional))):
   if passes((*full,*extra),True):return True
  return False
 def visit(a):
  if a==4:return judge()
  b=a//2;seen=set()
  for i in range(13):
   if not rem[i] or I[i]>>b&1:continue
   tag=I[i],history[i],rem[i],tuple((p>>i)&1 for p in P)
   if tag in seen:continue
   seen.add(tag);js=set()
   for j in range(13):
    if i==j or not rem[j] or I[j]>>b&1:continue
    jt=I[j],history[j],rem[j],tuple((p>>j)&1 for p in P)
    if jt<tag or jt in js:continue
    js.add(jt);rem[i]-=1;rem[j]-=1;history[i]|=1<<a;history[j]|=1<<a;arms.append((i,j))
    ok=visit(a+1)
    arms.pop();history[i]^=1<<a;history[j]^=1<<a;rem[i]+=1;rem[j]+=1
    if ok:return True
  return False
 return visit(0),stats
if __name__=='__main__':
 rr=[list(map(int,s.split())) for s in Path('allrows.tsv').read_text().splitlines()]
 for idx,r in sorted(enumerate(rr),key=lambda t:-t[1][1].bit_count()):
  if not r[2]:print(idx,r[0],check(r),flush=True)
