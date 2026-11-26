"""SAT for fixed graph of full AND output masks and remaining intermediates."""
import itertools,sys,time
from pysat.solvers import Solver
from pysat.formula import IDPool
ns=tuple(map(int,sys.argv[1])); tri=tuple(map(int,sys.argv[2]));targets=[{(i+k)%13 for k in (0,1,3,9)} for i in ns];U=sorted(set.union(*targets));T=[{U.index(q) for q in t} for t in targets];d=len(U)
assert len(ns)==6 and len(tri)==3 and set.intersection(*(T[t] for t in tri))
G={tri[0]:(0,1),tri[1]:(1,2),tri[2]:(0,2)}
for j,t in enumerate(sorted(set(range(6))-set(tri))):G[t]=(3,4+j)
m=10;P=range(7);extra=range(7,10)
s=Solver(name='cadical195');v=IDPool();V=lambda *args:v.id(args)
def oneof(xs):
 s.add_clause(xs)
 for a,b in itertools.combinations(xs,2):s.add_clause([-a,-b])
def union(z,xs):
 s.add_clause([-z,*xs])
 for x in xs:s.add_clause([-x,z])
def and2(z,x,y):s.append_formula([[-x,-y,z],[-z,x],[-z,y]])
def out(i,q):return V('o',i,q)
def src(i,k,j):return V('src',i,k,j)
def lt(i,j):return V('lt',i,j) if i<j else -V('lt',j,i)
for i,j,k in itertools.permutations(range(m),3):s.add_clause([-lt(i,j),-lt(j,k),lt(i,k)])
for i,j in itertools.combinations(extra,2):s.add_clause([lt(i,j)])
# Any full parent has at least two earlier nonparent ancestors.
for i in P:
 s.add_clause([lt(7,i)]);s.add_clause([lt(8,i)])
for t,(i,j) in G.items():
 for q in range(d):
    if q in T[t]:
        s.add_clause([out(i,q)]);s.add_clause([out(j,q)])
    else:s.add_clause([-out(i,q),-out(j,q)])
for i in range(m):
    opts=[-1]+[j for j in range(m) if j!=i]+[m+t for t,(a,b) in G.items() if i not in (a,b)]
    op=V('op',i)
    for k in (0,1):
        oneof([src(i,k,j) for j in opts])
        for t in T:
            for a,b in itertools.combinations(t,2):s.add_clause([-src(i,k,-1),-V('p',i,k,a),-V('p',i,k,b)])
        s.add_clause([-src(i,k,-1),op])
        for j in opts:
            if 0<=j<m:s.add_clause([-src(i,k,j),lt(j,i)])
            if j>=m:
                for p in G[j-m]:s.add_clause([-src(i,k,j),lt(p,i)])
    for j in opts:
        if j<0:continue
        for h in opts:
            if h<=j:s.add_clause([-src(i,0,j),-src(i,1,h)])
    for q in range(d):
        pairs=[V('p',i,k,q) for k in (0,1)];x,y=pairs;o=out(i,q)
        for k,p in enumerate(pairs):
            for j in opts:
                z=src(i,k,j)
                if j==-1:continue
                if j<m:
                    a=out(j,q);s.add_clause([-z,-p,a]);s.add_clause([-z,p,-a])
                else:s.add_clause([-z,p if q in T[j-m] else -p])
        s.append_formula([[op,-x,-y,o],[op,x,-o],[op,y,-o],[-op,x,y,-o],[-op,-x,o],[-op,-y,o]])
    hv=[]
    for t,A in enumerate(T):
        qq=V('hit',i,t);hv.append(qq);pairs=[]
        for a,b in itertools.combinations(sorted(A),2):
            z=V('ii',i,a,b);and2(z,out(i,a),out(i,b));pairs.append(z)
        union(qq,pairs)
        if i in extra:s.add_clause([-out(i,a) for a in A])
    for h in hv:s.add_clause([q for q in hv if q!=h])
    if i>=4:s.add_clause([src(j,k,i) for j in range(m) if j!=i for k in (0,1)])
print(ns,tri,flush=True);t=time.monotonic();r=s.solve();print(r,time.monotonic()-t,s.accum_stats(),flush=True)
if r:
 model=set(s.get_model())
 for i in range(m):print(i,'or' if V('op',i) in model else 'and', [next(j for j in range(-1,m+6) if src(i,k,j) in model) for k in (0,1)],[U[q] for q in range(d) if out(i,q) in model])
