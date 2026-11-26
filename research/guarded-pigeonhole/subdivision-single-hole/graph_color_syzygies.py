"""Count proper labeled 3-colorings via triangle reduction and rank-two bivectors."""
from itertools import combinations,product
from random import Random
from truth_projection import echelon,index,kernel,parity


def affine_solution(rows,n):
    piv={}
    for row,rhs in rows:
        while row and row.bit_length() in piv:
            v,w=piv[row.bit_length()]
            row^=v
            rhs^=w
        if not row:
            if rhs:return None
        else:piv[row.bit_length()]=row,rhs
    point=0
    for k,(r,w) in sorted(piv.items()):
        if parity(r&point)^w:point|=1<<(k-1)
    return point,kernel([r for r,_ in piv.values()],n)


def points(base,directions):
    value=base
    for i in range(1<<len(directions)):
        if i:value^=directions[(i&-i).bit_length()-1]
        yield value


def count(n,edges,mode='auto'):
    edges={tuple(sorted(e)) for e in edges}
    if any(u==v for u,v in edges):return 0,None
    active=sorted({v for e in edges for v in e})
    if not active:return 3**n,[1]*n
    pos={v:i for i,v in enumerate(active)}
    E={(pos[u],pos[v]) for u,v in edges}
    N=len(active)
    tris=[(1<<i)|(1<<j)|(1<<k) for i,j,k in combinations(range(N),3)
          if (i,j) in E and (i,k) in E and (j,k) in E]
    basis=kernel(tris,N)
    d=len(basis)
    P=[index(basis,1<<i) for i in range(N)]
    ij=list(combinations(range(d),2))
    def wedge(x,y):
        return sum(((((x>>i)&(y>>j))^((x>>j)&(y>>i)))&1)<<k for k,(i,j) in enumerate(ij))
    line=affine_solution([(wedge(P[i],P[j]),1) for i,j in E],len(ij))
    if line is None:return 0,None
    total=0
    witness=None
    if mode=='first' or (mode=='auto' and d<=len(line[1])):
        for a in range(1<<d):
            rows=[((P[j] if parity(a&P[i]) else 0)^(P[i] if parity(a&P[j]) else 0),1) for i,j in E]
            sol=affine_solution(rows,d)
            if sol:
                total+=1<<len(sol[1])
                witness=a,sol[0]
    else:
        for z in points(*line):
            rows=[0]*d
            for k,(i,j) in enumerate(ij):
                if z>>k&1:
                    rows[i]|=1<<j
                    rows[j]|=1<<i
            if len(echelon(rows))!=2:continue
            i,j=next((i,j) for i,j in ij if rows[i]>>j&1)
            witness=rows[i],rows[j]
            total+=6
    if witness:
        a,b=witness
        coloring=[1]*n
        for v,p in zip(active,P):coloring[v]=parity(a&p)|(parity(b&p)<<1)
        assert all(coloring) and all(coloring[i]!=coloring[j] for i,j in edges)
        witness=coloring
    return total*3**(n-N),witness


if __name__=='__main__':
    rng=Random(560)
    for _ in range(180):
        n=rng.randrange(1,7)
        E={e for e in combinations(range(n),2) if rng.randrange(2)}
        expected=sum(all(c[i]!=c[j] for i,j in E) for c in product(range(3),repeat=n))
        for mode in ('auto','first','bivector'):
            result,w=count(n,E,mode)
            assert result==expected and bool(w)==bool(result)
    # Every complete tripartite graph has precisely six colorings, however large its parts.
    for m in (3,6,10):
        E={e for e in combinations(range(3*m),2) if e[0]//m!=e[1]//m}
        assert count(3*m,E)[0]==6
    print('180 graph counts in both modes and 3 dense complete tripartite examples.')
