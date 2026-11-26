from random import Random
from itertools import product
rng=Random(2228)
def pivots(rows,p):
    basis={}; ids=[]
    for i,v in enumerate(rows):
        x=list(v)
        for j,row in sorted(basis.items()):x=[(u-x[j]*s)%p for u,s in zip(x,row)]
        j=next((j for j,u in enumerate(x) if u),None)
        if j is not None:
            ids.append(i);basis[j]=[u*pow(x[j],-1,p)%p for u in x]
    return ids
def make(i,j,signed):
    if j-i==1:return i
    h=rng.randrange(i+1,j)
    pat=rng.choice([None,(1,1),(0,1),(1,0),(0,0)] if signed else [None,(1,1)])
    return make(i,h,signed),make(h,j,signed),pat
def brute(tree):
    if type(tree)==int:return [[0],[1]]
    a,b,q=tree
    return [x+y for x in brute(a) for y in brute(b) if q is None or q[0] not in x or q[1] not in y]
for case in range(60):
    n=m=5; p=[2,3,5][case%3]
    X=make(0,n,False);Y=make(0,m,True)
    pins=[frozenset((j,rng.randrange(2)) for j in range(m) if rng.randrange(4)==0) for i in range(n)]
    def rowbasis(rows):
        def walk(t):
            if type(t)==int:return {1<<s:[tuple(int((t,1-s) not in R) for R in rows)] for s in range(2)}
            a,b,q=t;answer={}
            for u,us in walk(a).items():
                for v,vs in walk(b).items():
                    if q and u>>q[0]&1 and v>>q[1]&1:continue
                    answer.setdefault(u|v,[]).extend(tuple(x*y for x,y in zip(c,d)) for c in us for d in vs)
            return {k:[V[i] for i in pivots(V,p)] for k,V in answer.items()}
        cols=sum(walk(Y).values(),[])
        return [rows[i] for i in pivots([tuple(c[j] for c in cols) for j in range(len(rows))],p)]
    def walkX(t):
        if type(t)==int:return {1:[frozenset()],2:[pins[t]]}
        a,b,q=t;out={}
        for u,us in walkX(a).items():
            for v,vs in walkX(b).items():
                if q and u>>1&1 and v>>1&1:continue
                out.setdefault(u|v,[]).extend(c|d for c in us for d in vs)
        return {k:rowbasis(v) for k,v in out.items()}
    got=len(rowbasis(sum(walkX(X).values(),[])))
    mat=[]
    for x in brute(X):
        R=frozenset().union(*(pins[i] for i,v in enumerate(x) if v))
        mat.append([int(all(y[j]==v for j,v in R)) for y in brute(Y)])
    assert got==len(pivots(mat,p))
print('60 signed two-shore basis contractions verified over F2,F3,F5')
