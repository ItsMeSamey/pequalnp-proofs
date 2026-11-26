"""Small exact tests. LP feasibility here enumerates basic supports; it is not the runtime theorem's LP implementation."""
from fractions import Fraction as Q
from itertools import combinations, product
from random import Random
from affine_cover_solver import insert


def size(n,flat):
    piv={}
    return (1<<(n-len(piv))) if not flat else cell_size(n,flat,piv)


def cell_size(n,flat,piv):
    for m,b in flat:
        if not insert(m,b,piv):
            return 0
    return 1<<(n-len(piv))


def values(n,f):
    return tuple(sum(w for w,flat in f if all(((x&m).bit_count()&1)==b for m,b in flat)) for x in range(1<<n))


def gram(n,functions):
    return [[sum(u*v*size(n,a+b) for u,a in f for v,b in g) for g in functions] for f in functions]


def independent_solve(a,b,variables):
    mat=[list(map(Q,row))+[Q(z)] for row,z in zip(a,b)]
    piv=[]
    for j in range(variables):
        i=len(piv)
        q=next((q for q in range(i,len(mat)) if mat[q][j]),None)
        if q is None:continue
        mat[i],mat[q]=mat[q],mat[i]
        d=mat[i][j];mat[i]=[v/d for v in mat[i]]
        for h,r in enumerate(mat):
            if h!=i and r[j]:
                t=r[j];mat[h]=[v-t*u for v,u in zip(r,mat[i])]
        piv.append(j)
    if any(not any(r[:-1]) and r[-1] for r in mat):
        return None,piv
    sol=[Q(0)]*variables
    for i,j in enumerate(piv):
        sol[j]=mat[i][-1]
    return sol,piv


def redundant(columns,i):
    rest=[j for j in range(len(columns)) if i!=j]
    for k in range(1,len(rest)+1):
        for cols in combinations(rest,k):
            a=list(zip(*(columns[j]+(1,) for j in cols)))
            sol,p=independent_solve(a,columns[i]+(1,),k)
            if sol is not None and len(p)==k and min(sol)>=0:
                return True
    return False


def audit_zonotopes():
    edges=[(u,u^(1<<i)) for u in range(8) for i in range(3) if not u>>i&1]
    rng=Random(629)
    eps={e:rng.choice((-1,1)) for e in edges}
    for A in combinations(range(8),4):
        B=[v for v in range(8) if v not in A]
        G=[[eps.get(tuple(sorted((a,b))),0) for b in B] for a in A]
        _,rows=independent_solve(list(zip(*G)),[0]*4,4)
        k=len(rows); pts=set()
        for s in product((-1,1),repeat=4):
            pts.add(tuple(sum(w*G[j][i] for j,w in enumerate(s)) for i in range(4)))
        exposed=set()
        for signs in product((-1,1),repeat=k):
            w,_=independent_solve([G[j] for j in rows],signs,4)
            exposed.add(max(pts,key=lambda x:(sum(t*v for t,v in zip(w,x)),x)))
        assert len(exposed)==2**k
        # Direct parities: half the signed crossing spin sums are Walsh singleton coefficients.
        for s in (tuple([1]*4),tuple([-1,1,-1,1])):
            sums=[0]*4
            for t in product((-1,1),repeat=4):
                spins=dict(zip(A,s));spins.update(zip(B,t))
                f=sum(1 for u,v in edges if spins[u]*spins[v]==eps[u,v])
                for j in range(4):sums[j]+=t[j]*f
            assert all(sums[i]==8*sum(w*G[j][i] for j,w in enumerate(s)) for i in range(4))


if __name__=='__main__':
    rng=Random(71)
    for _ in range(25):
        n=rng.randrange(1,4)
        fs=[[(Q(rng.randrange(-3,4),rng.randrange(1,4)),tuple((rng.randrange(1<<n),rng.randrange(2))
               for j in range(rng.randrange(3)))) for l in range(rng.randrange(1,4))] for i in range(4)]
        fs.append([(w/2,flat) for f in fs[:2] for w,flat in f])
        G=gram(n,fs);V=[values(n,f) for f in fs]
        assert G==[[sum(a*b for a,b in zip(v,w)) for w in V] for v in V]
        # Direct residual and Gram-coordinate hull membership agree.
        C=[tuple(row) for row in G]
        for i in (0,4):
            assert redundant(V,i)==redundant(C,i)
        assert redundant(C,4)
    # The entire dyadic segment has exactly its two endpoints as vertices.
    for a in range(16):
        t=Q(a,15)
        f=lambda c: (0,1,c,1+c)
        assert tuple((1-t)*u+t*v for u,v in zip(f(0),f(15)))==f(a)
    audit_zonotopes()
    print('25 signed rational Gram/hull systems, a 16-point dyadic line and all 70 balanced cube cuts passed')
