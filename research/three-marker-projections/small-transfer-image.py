import runpy,itertools,collections,functools
from pathlib import Path
c=runpy.run_path(str(Path(__file__).with_name('three-transfer-simplices.py')))
m=lambda S:sum(1<<i for i in S)
bits=lambda s:[i for i in range(16) if s>>i&1]
def fac(d):return next(i for i in (d%4,d//4) if i),int(bool(d%4))+2*bool(d//4)
ed=[x for x in range(1,16) if x not in c['invertible']]
sub=([],[1],[2],[3]); adj=[m(x^d for d in ed) for x in range(16)]
rules=[[m(x^d for d in ed if (fac(d)[0] in w)==(fac(d)[1] in v)) for w in sub for v in sub] for x in range(16)]
tests=[m(p) for p in c['tests']];gs=collections.defaultdict(list)
for s in range(65536):
 if not 5<=s.bit_count()<=6:continue
 xs=bits(s)
 if any(not s&r for x in xs for r in rules[x]) or not c['full'](xs):continue
 q=1<<xs[0]
 while True:
  z=q
  for x in bits(q):z|=s&adj[x]
  if z==q:break
  q=z
 if q==s:gs[sum(bool(s&t)<<i for i,t in enumerate(tests))].append(s)

candidates={s for group in gs.values() for s in group}
P=[set(bits(i)) for i in range(1,16)]
def image(a,b,d):
    return m({x+4*y for x in a for y in b}|{x+4*(x^z) for x in a for z in d}|{(y^z)+4*y for y in b for z in d})
phys={image(a,b,d) for a,b,d in itertools.product(P,repeat=3)}
real={s for s in phys if s.bit_count() in (5,6) and c['full'](bits(s))}
assert real<=candidates
assert candidates-real=={m(x^a for x in c['invertible']) for a in range(16)}
assert collections.Counter(s.bit_count() for s in real)=={5:144,6:288}
simplex={0,1,2,4,8}
def action(x,L,R):
    return c['apply'](L,c['apply'](x,c['apply'](R,1)))+4*c['apply'](L,c['apply'](x,c['apply'](R,2)))
assert {m(action(x,L,R)^a for x in simplex) for L,R,a in itertools.product(c['invertible'],c['invertible'],range(16))}=={s for s in real if s.bit_count()==5}
X=image({0,2},{0,1},{0,3}); Z=image({0,2},{0,1},{0,2,3}); Y=image({1},{2},{1,2,3})
assert X&~Z==0 and Z^X==m([7,8]) and not X&Y and Z&Y==m([8])
assert all(bool(X&t)==bool(Z&t) for t in tests)
print(len(real),len(candidates),bits(X),bits(Z),bits(Y))
