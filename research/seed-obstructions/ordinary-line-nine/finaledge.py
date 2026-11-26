from compartments import test
from joint import joint
from edge import *
from itertools import permutations
def perm(mask,seq):return sum(bool(mask&1<<i)<<j for i,j in enumerate(seq))
def group():
 pts=[sum(bool(s&1<<p)<<j for j,s in enumerate(ss)) for p in range(13)]
 assert len(set(pts))==13
 nn=set(ns);nn={(p,l) for p,l in nn if not any((p,l)!=(q,m) and p&~q==0 and l&~m==0 for q,m in nn)}
 grp=[]
 for g in permutations(range(7)):
  qq=[perm(z,g) for z in pts]
  if set(qq)!=set(pts):continue
  pp=[pts.index(z) for z in qq]
  if {(perm(p,pp),perm(l,g)) for p,l in nn}==nn:grp.append(g)
 assert len(grp)==24
 return grp
def geometry(a,b,t,u):
 sig=[(bool(a&1<<j),bool(b&1<<j)) for j in range(7)]
 act=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
 sq=[sum(1<<p for p in inside(s) if points[p]&act[j]) for j,s in enumerate(ss)]
 hit=[pc[s] for s in sq]
 outer=set(range(7))-{t,u}
 assert all(sq)
 # No bare loose-line OR attachment: attach at a resident jointly pivotal singleton.
 assert all(any((points[p]&lc[a]&lc[b]) for p in inside(s)) for s in sq)
 # Assign the ancestor R-only guard to u. It can then use u as a fixed
 # special companion for any ordinary j. Other dropped guards use one common
 # outside companion or u itself, since their resident scopes are nested.
 assert all(all(m&hit[u]&hit[v] for m in pairs[j]) for j in outer for v in outer-{j})
 assert all(any(m&hit[u] for m in [n]) for j in outer for n in pairs[j])
 # Both-exterior children never see the extra bits. The guard assigned to u
 # supplies the only unconstrained R bit. All remaining ancestors can pass
 # using t's pivotal singleton on this negative.
 assert all(m&hit[t] for m in pairs[u])
 # Certify the point-pinning lemma whenever the joint ancestor has an outside
 # resident. It eliminates both blocked lines' common defective point.
 common=ss[t]&ss[u]
 assert common.bit_count()==1
 for j in outer:
  forced=union(act[k]&hit[k] for k in (t,u,j))
  assert all(points[x]&forced for x in inside(common))
 # Hence at most two ordinary defects, at most one for t, three for a raw u.
 assert sum((ss[j]^sq[j]).bit_count() for j in outer)==2
 assert (ss[t]&~sq[t]&~common).bit_count()==1
if __name__=='__main__':
 hard=[]
 for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
  h=failures(a,b)
  if len(h)!=1:continue
  m=sum(1<<j for j in h[0]);r=b if a==m else a
  if analyze(a,b)[0]!='budget':continue
  hard.append((m,r))
  t=next(j for j in h[0] if r>>j&1);u=next(j for j in h[0] if j!=t)
  geometry(m,r,t,u)
  assert all(r0+pen<=6 for _,r0,pen in joint(m,r))
 grp=group(); reps=sorted({min((perm(a,g),perm(b,g)) for g in grp) for a,b in hard})
 print('Hard banks',len(hard),'orbits',reps,flush=True)
 for a,b in reps:
  t=next(j for j in range(7) if (a&b)>>j&1);u=next(j for j in range(7) if (a&~b)>>j&1)
  print('Testing',a,b,t,u,flush=True)
  for loc in product(range(3),repeat=2):
   assert not test(a,b,t,u,loc,threshold=6,no_or=True),(a,b,loc,'no OR')
   if loc!=(2,2):assert not test(a,b,t,u,loc,threshold=7),(a,b,loc,'paid OR')
  print('Passed 17 UNSAT checks',flush=True)
