import sys,itertools,time
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
ns=list(map(int,sys.argv[1]));n=int(sys.argv[2]);raw=[{(i+d)%13 for d in (0,1,3,9)} for i in ns];U=sorted(set.union(*raw));T=[{U.index(q) for q in t} for t in raw];d=len(U);k=len(T)
v=IDPool();s=Solver(name='cadical195');V=lambda *args:v.id(args)
def oneof(xs):
 s.add_clause(xs)
 for x,y in itertools.combinations(xs,2):s.add_clause([-x,-y])
def and2(z,x,y):s.append_formula([[-x,-y,z],[x,-z],[y,-z]])
def orlist(z,xs):
 s.add_clause([-z,*xs])
 for x in xs:s.add_clause([-x,z])
def eqif(b,x,y):s.append_formula([[-b,-x,y],[-b,x,-y]])
def out(i,j):return V('o',i,j)
def hit(i,t):return V('hit',i,t)
def h(i):return V('op',i)
def src(i,k,j):return V('src',i,k,j)
def end(t,i):return V('end',t,i)
for i in range(n):
 for k0 in (0,1):
    oneof([src(i,k0,j) for j in range(-1,i)])
    for t in T:
        for a,b in itertools.combinations(t,2):s.add_clause([-src(i,k0,-1),-V('p',i,k0,a),-V('p',i,k0,b)])
 for j in range(i):
    for jj in range(-1,j):s.add_clause([-src(i,0,j),-src(i,1,jj)])
 # topologically sort by maximum source index, tie break using minimum index
 if i:
    for j in range(i-1):
        for jj in range(-1,j):s.add_clause([-src(i-1,1,j),-src(i,1,jj)])
    for j in range(-1,i-1):
        for l in range(j):
            for ll in range(-1,l):s.add_clause([-src(i-1,1,j),-src(i,1,j),-src(i-1,0,l),-src(i,0,ll)])
    # When both gates are formed from 2 free masks, order the result masks.
    cond=src(i,1,-1);prefix=cond
    for a in range(d):
        x=out(i-1,a);y=out(i,a);s.add_clause([-prefix,-x,y])
        b=V('pre',i,a)
        s.add_clause([-prefix,-x,-y,b]);s.add_clause([-prefix,x,y,b]);prefix=b
 for a in range(d):
    x,y=(V('p',i,j,a) for j in (0,1));o=out(i,a)
    for k0,p in enumerate([x,y]):
        for j in range(i):eqif(src(i,k0,j),p,out(j,a))
    for c in ((h(i),-x,-y,o),(h(i),x,-o),(h(i),y,-o),(-h(i),x,y,-o),(-h(i),-x,o),(-h(i),-y,o)):s.add_clause(c)
 for t,A in enumerate(T):
    ps=[]
    for a,b in itertools.combinations(sorted(A),2):
        p=V('pair',i,a,b);and2(p,out(i,a),out(i,b));ps.append(p)
    orlist(hit(i,t),ps)
 s.add_clause([hit(i,t) for t in range(len(T))])
 s.add_clause([end(t,i) for t in range(len(T))]+[src(j,k0,i) for j in range(i+1,n) for k0 in (0,1)])
for t,A in enumerate(T):
 zeros=set(range(d))-A
 oneof([end(t,i) for i in range(3,n)])
 for i in range(min(3,n)):s.add_clause([-end(t,i)])
 for i in range(n):
    e=end(t,i)
    for a in range(d):s.add_clause([-e,out(i,a) if a in A else -out(i,a)])
    # OR-root must use exactly one free singleton and one three-point AND.
    s.add_clause([-e,-h(i),src(i,0,-1)])
    s.add_clause([-e,-h(i),-src(i,1,-1)])
    for j in range(i):
        u=src(i,1,j)
        s.add_clause([-e,-h(i),-u,-h(j)])
        s.add_clause([-e,-h(i),-u,*[-out(j,a) for a in A]])
        for a,b in itertools.combinations(A,2):s.add_clause([-e,-h(i),-u,out(j,a),out(j,b)])
# All proper subfamilies need three gates per target after deleting transversal masks.
for m in range(1,len(T)):
 for group in itertools.combinations(range(len(T)),m):
    paid=[]
    for i in range(n):
        q=V('keep',group,i);paid.append(q);orlist(q,[hit(i,t) for t in group])
    s.append_formula(CardEnc.atleast(paid,({1:4,2:8,3:12}.get(m,3*m)),vpool=v,encoding=EncType.seqcounter))
if len(T)==4 and n==13:
 for i in range(n):
    for t in range(len(T)):s.add_clause([-end(t,i),-h(i)])
    for t in range(len(T)):
        s.add_clause([end(t,i),*[hit(i,u) for u in range(len(T)) if u!=t]])
print(ns,n,flush=True);tic=time.monotonic();res=s.solve();print(res,time.monotonic()-tic,s.accum_stats(),flush=True)
if res:
 model=set(s.get_model())
 for i in range(n):print(i+1,'or' if h(i) in model else 'and',[next(j for j in range(-1,i) if src(i,k0,j) in model) for k0 in (0,1)],[U[j] for j in range(d) if out(i,j) in model])
