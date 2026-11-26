import sys,itertools,time
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.formula import CNF
import argparse, hashlib, pathlib
import pysat
def build(ns,n):
    raw=[{(i+d)%13 for d in (0,1,3,9)} for i in ns]
    U=sorted(set.union(*raw));T=[{U.index(q) for q in t} for t in raw];d=len(U)
    v=IDPool();s=CNF();V=lambda *args:v.id(args)
    def oneof(xs):
     s.append(xs)
     for x,y in itertools.combinations(xs,2):s.append([-x,-y])
    def and2(z,x,y):s.extend([[-x,-y,z],[x,-z],[y,-z]])
    def orlist(z,xs):
     s.append([-z,*xs])
     for x in xs:s.append([-x,z])
    def eqif(b,x,y):s.extend([[-b,-x,y],[-b,x,-y]])
    def out(i,j):return V('o',i,j)
    def hit(i,t):return V('hit',i,t)
    def h(i):return V('op',i)
    def src(i,k,j):return V('src',i,k,j)
    def end(t,i):return V('end',t,i)
    for i in range(n):
     for k0 in (0,1):
        oneof([src(i,k0,j) for j in range(-1,i)])
        for t in T:
            for a,b in itertools.combinations(t,2):s.append([-src(i,k0,-1),-V('p',i,k0,a),-V('p',i,k0,b)])
     for j in range(i):
        for jj in range(-1,j):s.append([-src(i,0,j),-src(i,1,jj)])
     # topologically sort by maximum source index, tie break using minimum index
     if i:
        for j in range(i-1):
            for jj in range(-1,j):s.append([-src(i-1,1,j),-src(i,1,jj)])
        for j in range(-1,i-1):
            for l in range(j):
                for ll in range(-1,l):s.append([-src(i-1,1,j),-src(i,1,j),-src(i-1,0,l),-src(i,0,ll)])
        # When both gates are formed from 2 free masks, order the result masks.
        cond=src(i,1,-1);prefix=cond
        for a in range(d):
            x=out(i-1,a);y=out(i,a);s.append([-prefix,-x,y])
            b=V('pre',i,a)
            s.append([-prefix,-x,-y,b]);s.append([-prefix,x,y,b]);prefix=b
     for a in range(d):
        x,y=(V('p',i,j,a) for j in (0,1));o=out(i,a)
        for k0,p in enumerate([x,y]):
            for j in range(i):eqif(src(i,k0,j),p,out(j,a))
        for c in ((h(i),-x,-y,o),(h(i),x,-o),(h(i),y,-o),(-h(i),x,y,-o),(-h(i),-x,o),(-h(i),-y,o)):s.append(c)
     for t,A in enumerate(T):
        ps=[]
        for a,b in itertools.combinations(sorted(A),2):
            p=V('pair',i,a,b);and2(p,out(i,a),out(i,b));ps.append(p)
        orlist(hit(i,t),ps)
     s.append([hit(i,t) for t in range(len(T))])
     s.append([end(t,i) for t in range(len(T))]+[src(j,k0,i) for j in range(i+1,n) for k0 in (0,1)])
    for t,A in enumerate(T):
     zeros=set(range(d))-A
     oneof([end(t,i) for i in range(3,n)])
     for i in range(min(3,n)):s.append([-end(t,i)])
     for i in range(n):
        e=end(t,i)
        for a in range(d):s.append([-e,out(i,a) if a in A else -out(i,a)])
        # OR-root must use exactly one free singleton and one three-point AND.
        s.append([-e,-h(i),src(i,0,-1)])
        s.append([-e,-h(i),-src(i,1,-1)])
        for j in range(i):
            u=src(i,1,j)
            s.append([-e,-h(i),-u,-h(j)])
            s.append([-e,-h(i),-u,*[-out(j,a) for a in A]])
            for a,b in itertools.combinations(A,2):s.append([-e,-h(i),-u,out(j,a),out(j,b)])
    # Restriction retains the paid marks and eliminates every transversal gate.
    for m in range(1,len(T)):
     for group in itertools.combinations(range(len(T)),m):
        paid=[]
        for i in range(n):
            q=V('keep',group,i);paid.append(q);orlist(q,[hit(i,t) for t in group])
        s.extend(CardEnc.atleast(paid,{1:4,2:8}[m],vpool=v,encoding=EncType.seqcounter))
    return s

def incidence_type(lines):
    return min(tuple(sorted(sum(1<<j for j,t in enumerate(order) if p in t)
                            for p in range(13))) for order in itertools.permutations(lines))

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--solver",default="cadical195")
    parser.add_argument("--export",type=pathlib.Path)
    opts=parser.parse_args()
    base=[{(i+d)%13 for d in (0,1,3,9)} for i in range(7)]
    assert all(len(t)==4 for t in base)
    assert all(len(a&b)==1 for a,b in itertools.combinations(base,2))
    assert max(sum(p in t for t in base) for p in range(13))==3
    cases=[((0,1),7),((0,1,3),11),((0,1,5),11)]
    for size in (2,3):
        got={incidence_type(x) for x in itertools.combinations(base,size)}
        expected={incidence_type([base[i] for i in ids]) for ids,n in cases if len(ids)==size}
        assert got==expected
    print("python",sys.version.split()[0],"python-sat",pysat.__version__,"solver",opts.solver,flush=True)
    for ids,n in cases:
        formula=build(ids,n)
        dimacs=formula.to_dimacs().encode()
        if opts.export:
            opts.export.mkdir(parents=True,exist_ok=True)
            (opts.export/("marked-"+"".join(map(str,ids))+".cnf")).write_bytes(dimacs)
        with Solver(name=opts.solver,bootstrap_with=formula) as solver:
            result=solver.solve()
            conflicts=solver.accum_stats().get("conflicts")
        print("lines",ids,"gates",n,"variables",formula.nv,"clauses",len(formula.clauses),
              "sha256",hashlib.sha256(dimacs).hexdigest(),"SAT",result,"conflicts",conflicts,flush=True)
        assert result is False
    print("Both marked minima and the seven-line incidence geometry checked.")
