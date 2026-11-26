import itertools,time,sys,pickle
from functools import lru_cache
from collections import Counter
from pysat.solvers import Solver
from pysat.formula import IDPool

def parts(lst):
 if not lst:yield [];return
 a,*rest=lst
 for p in parts(rest):
    yield [(a,)]+p
    for i,b in enumerate(p): yield p[:i]+[(a,*b)]+p[i+1:]

def fullgraphs(F,L):
 for groups in parts(F):
    options=[[0,1,2,3,4] if len(g)==3 and set.intersection(*(L[i] for i in g)) else [0] for g in groups]
    for choices in itertools.product(*options):
        v=0;edges={}
        for g,tri in zip(groups,choices):
            if tri==1:
                for j,i in enumerate(g):edges[i]=(v+j,v+(j+1)%3)
                v+=3
            elif tri>=2:
                mid=g[tri-2];a,b=[t for t in g if t!=mid]
                edges[a]=(v,v+1);edges[mid]=(v+1,v+2);edges[b]=(v+2,v+3);v+=4
            else:
                for j,i in enumerate(g,1):edges[i]=(v,v+j)
                v+=len(g)+1
        yield edges,v

def addtrips(G,v,ids):
 if not ids:yield G,v;return
 t,*rest=ids
 for a,b in itertools.combinations(range(v+2),2):
    if a<v and b==v+1:continue
    if any({a,b}==set(e) for e in G.values()):continue
    yield from addtrips(G|{t:(a,b)},max(v,b+1),rest)

def possibilities(ns,n):
 L=[{(i+d)%13 for d in (0,1,3,9)} for i in ns];k=len(L);seen=set()
 inc=sorted(sum(1<<t for t,A in enumerate(L) if x in A) for x in range(13))
 perms=[f for f in itertools.permutations(range(k)) if sorted(sum(1<<f[t] for t,A in enumerate(L) if x in A) for x in range(13))==inc]
 for r in range(2):
  for S in itertools.combinations(range(k),r):
   F=[i for i in range(k) if i not in S]
   for P,p in fullgraphs(F,L):
    if p>n-k-r-(2 if r else 3):continue
    for G,v in addtrips(P,p,S):
     D=n-k-r;Q=D-v
     if Q < (2 if r else 3):continue
     # canonical renumber vertices by incident output labels
     signatures=[tuple(t for t in range(k) if i in G[t]) for i in range(v)]
     # Two degree-one vertices of the same isolated edge have equal signature.
     key=tuple(sorted(signatures))
     if (S,key) in seen:continue
     for perm in perms:
        ren=tuple(sorted(tuple(sorted(perm[t] for t in sig)) for sig in key))
        seen.add((tuple(sorted(perm[t] for t in S)),ren))
     allowed=[]
     for drop in itertools.product(*(L[t] for t in S)):
        C=[u.copy() for u in L]
        for t,p in zip(S,drop):C[t].remove(p)
        M=[set.union(*(C[t] for t in signatures[i])) for i in range(v)]
        if any(M[a]&M[b]!=C[t] for t,(a,b) in G.items()):continue
        whole=set.union(*L)
        if any(m==whole for m in M):continue
        # Each parent properly exceeds the core, and cannot equal any target or other core.
        possible=True
        for i,lo in enumerate(M):
            hi=whole.copy()
            for t in signatures[i]:
                a,b=G[t];other=b if a==i else a;hi-=M[other]-C[t]
            if lo==hi and (lo in L or lo in C):possible=False;break
            if r and sum(len(hi&L[t])>=2 for t in F)<2:possible=False;break
        if possible:allowed.append(drop)
     if allowed:yield S,G,v,Q,allowed

def run(ns,S,G,vp,Q,drops,corelimit=0):
 U=sorted(set.union(*[{(i+d)%13 for d in (0,1,3,9)} for i in ns]));T=[{U.index((i+d)%13) for d in (0,1,3,9)} for i in ns];k=len(T);D=len(U);m=vp+Q
 v=IDPool();s=Solver(name='cadical195');V=lambda *args:v.id(args)
 def one(q):
    s.add_clause(q)
    for x,y in itertools.combinations(q,2):s.add_clause([-x,-y])
 def OR(q,xx):
    s.add_clause([-q,*xx])
    for x in xx:s.add_clause([-x,q])
 def AND(q,x,y):s.append_formula([[-q,x],[-q,y],[q,-x,-y]])
 def out(i,a):return V(0,i,a)
 def src(i,p,j):return V(1,i,p,j)
 def lt(i,j):return V(2,i,j) if i<j else -V(2,j,i)
 def core(t,a):return V(3,t,a)
 for a,b,c in itertools.permutations(range(m),3):s.add_clause([-lt(a,b),-lt(b,c),lt(a,c)])
 for a,b in itertools.combinations(range(vp,m),2):s.add_clause([lt(a,b)])
 for a in range(vp):
    for b in range(vp,vp+(1 if S else 2)):s.add_clause([lt(b,a)])
 masks=[V(4,j) for j in range(len(drops))];one(masks)
 for j,drop in enumerate(drops):
    for t,point in zip(S,drop):
        for a in T[t]:s.add_clause([-masks[j],-core(t,a) if U[a]==point else core(t,a)])
 if Q==2 and k==7:
    # Each threshold-three seed requires one of the two distinct,
    # disjoint unions of free masks. Both may be put first.
    for g in range(vp,m):
        for port in (0,1):s.add_clause([src(g,port,-1)])
        for a in range(vp):s.add_clause([lt(g,a)])
    for q in range(D):s.add_clause([-out(vp,q),-out(vp+1,q)])
 for t,(a,b) in G.items():
    for q in range(D):
        if t in S and q in T[t]:AND(core(t,q),out(a,q),out(b,q))
        elif q in T[t]:s.add_clause([out(a,q)]);s.add_clause([out(b,q)])
        else:s.add_clause([-out(a,q),-out(b,q)])
 for i in range(m):
    opts=[-1]+[j for j in range(m) if j!=i]+[m+t for t in range(k) if i not in G[t]]+[m+k+t for t in S if i not in G[t]]
    op=V(5,i)
    for p in (0,1):
        one([src(i,p,j) for j in opts])
        for t in T:
            for a,b in itertools.combinations(t,2):s.add_clause([-src(i,p,-1),-V(6,i,p,a),-V(6,i,p,b)])
        s.add_clause([-src(i,p,-1),op])
        for j in opts:
            if 0<=j<m:s.add_clause([-src(i,p,j),lt(j,i)])
            if j>=m:
                for prev in G[(j-m)%k]:s.add_clause([-src(i,p,j),lt(prev,i)])
    for j in opts:
        if j>=0:
            for h in opts:
                if h<=j:s.add_clause([-src(i,0,j),-src(i,1,h)])
    for a in range(D):
        x,y=[V(6,i,p,a) for p in (0,1)];o=out(i,a)
        for p,xp in enumerate((x,y)):
            for j in opts:
                if j<0:continue
                z=src(i,p,j)
                if j<m or (j>=m+k and a in T[j-m-k]):
                    val=out(j,a) if j<m else core(j-m-k,a)
                    s.add_clause([-z,-xp,val]);s.add_clause([-z,xp,-val])
                else:s.add_clause([-z,xp if j<m+k and a in T[j-m] else -xp])
        s.append_formula([[op,-x,-y,o],[op,x,-o],[op,y,-o],[-op,x,y,-o],[-op,-x,o],[-op,-y,o]])
    hh=[]
    for t,A in enumerate(T):
        pairs=[]
        for a,b in itertools.combinations(sorted(A),2):
            z=V(7,i,a,b);AND(z,out(i,a),out(i,b));pairs.append(z)
        h=V(8,i,t);OR(h,pairs);hh.append(h)
    s.add_clause(hh)
    for zs in range(1,k):
        lower={1:4,2:8,3:12,4:14,5:15,6:18}[zs]
        for keep in itertools.combinations(range(k),zs):
            remaining=(m+k+len(S))-(k-zs)-len(set(S)-set(keep))
            if remaining<lower:s.add_clause([])
            if remaining==lower:s.add_clause([hh[t] for t in keep])
    if i>=vp:s.add_clause([src(l,p,i) for l in range(m) if l!=i for p in (0,1)])
 for t in range(k):
    ex=[]
    for i in range(m):
        x=V(9,i,t);OR(-x,[V(8,i,h) for h in range(k) if h!=t]);ex.append(x)
    if t in S:
        for x in ex:s.add_clause([-x])
    else:
        for x,y in itertools.combinations(ex,2):s.add_clause([-x,-y])
 if corelimit:
    s.conf_budget(corelimit);result=s.solve_limited()
 else:result=s.solve()
 model=s.get_model() if result else None;s.delete()
 return result,model

if __name__=='__main__':
 geom=tuple(map(int,sys.argv[1]));n=int(sys.argv[2]);jobs=list(possibilities(geom,n))
 print(geom,n,'graph instances',Counter((len(S),v) for S,G,v,Q,drop in jobs),flush=True)
 if len(sys.argv)>3:
    for i,(S,G,v,Q,drop) in enumerate(jobs):
        tic=time.monotonic();r,_=run(geom,S,G,v,Q,drop,int(sys.argv[3]))
        print(i,S,tuple(G.values()),v,Q,len(drop),r,round(time.monotonic()-tic,3),flush=True)
        if r:break
