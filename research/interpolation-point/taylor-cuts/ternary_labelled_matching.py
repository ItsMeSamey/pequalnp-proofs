"""One-sided witness search for perfect matchings labelled over F3^b."""
from functools import lru_cache
from itertools import product
from pathlib import Path
from secrets import randbelow
import sys
sys.path.append(str(Path(__file__).resolve().parents[2]/"direct-sat-algebra"/"scalar-field"))
from punctured_witness import BinaryField


@lru_cache(maxsize=8)
def _field(n):
    degree=2
    while (1<<degree)<n:
        degree+=2
    for modulus in range((1<<degree)+1,1<<(degree+1),2):
        try:
            f=BinaryField(modulus)
            break
        except ValueError:
            continue
    root=next(x for x in range(2,f.size) if (f.mul(x,x)^x^1)==0)
    return f,(1,root,root^1)


def _pfaffian(a,f):
    total=1
    for i in range(0,len(a),2):
        j=next((v for v in range(i+1,len(a)) if a[i][v]),None)
        if j is None:
            return 0
        if j!=i+1:
            a[i+1],a[j]=a[j],a[i+1]
            for row in a:
                row[i+1],row[j]=row[j],row[i+1]
        total=f.mul(total,a[i][i+1])
        inv=f.inverse(a[i][i+1])
        for u in range(i+2,len(a)):
            for v in range(u+1,len(a)):
                delta=f.mul(a[i][u],a[i+1][v])^f.mul(a[i][v],a[i+1][u])
                a[u][v]^=f.mul(inv,delta)
                a[v][u]=a[u][v]
    return total


def _evaluate(vertices,edges,target,weights,f,roots):
    pos={v:i for i,v in enumerate(vertices)}
    remaining=[(pos[u],pos[v],g,w) for (u,v,g),w in zip(edges,weights) if u in pos and v in pos]
    total=0
    for chi in product(range(3),repeat=len(target)):
        matrix=[[0]*len(pos) for _ in pos]
        for i,j,g,w in remaining:
            phase=sum(x*y for x,y in zip(chi,g))%3
            matrix[i][j]^=f.mul(w,roots[phase])
            matrix[j][i]=matrix[i][j]
        phase=-sum(x*y for x,y in zip(chi,target))%3
        total^=f.mul(_pfaffian(matrix,f),roots[phase])
    return total


def search(n,edges,target,*,rounds=1,randbelow_fn=randbelow):
    """Return ('SAT',original edge-index tuple) or ('UNKNOWN',None).

    Independent uniform field draws per edge and round give the RP bound.
    Parallel edges are distinct. Vertices are 0-based; each label is a trit tuple.
    """
    if type(n) is not int or n<0 or type(rounds) is not int or rounds<1:
        raise ValueError("invalid size or rounds")
    target=tuple(target)
    edges=[(u,v,tuple(g)) for u,v,g in edges]
    if any(type(x) is not int or not 0<=x<3 for x in target):
        raise ValueError("invalid target")
    for u,v,g in edges:
        if (any(type(i) is not int or not 0<=i<n for i in (u,v)) or u==v or
            len(g)!=len(target) or any(type(x) is not int or not 0<=x<3 for x in g)):
            raise ValueError("invalid edge")
    if n%2:
        return "UNKNOWN",None
    f,roots=_field(n)
    for _ in range(rounds):
        weights=tuple(randbelow_fn(f.size) for _ in edges)
        if any(type(x) is not int or not 0<=x<f.size for x in weights):
            raise ValueError("invalid random draw")
        vertices=set(range(n))
        residual=target
        if not _evaluate(vertices,edges,residual,weights,f,roots):
            continue
        chosen=[]
        while vertices:
            u=min(vertices)
            for k,(a,b,g) in enumerate(edges):
                if u not in (a,b) or not weights[k] or a not in vertices or b not in vertices:
                    continue
                rest=vertices-{a,b}
                goal=tuple((x-y)%3 for x,y in zip(residual,g))
                if _evaluate(rest,edges,goal,weights,f,roots):
                    chosen.append(k)
                    vertices,residual=rest,goal
                    break
            else:
                raise AssertionError("nonzero pivot has no nonzero matching restriction")
        if sorted(v for k in chosen for v in edges[k][:2])!=list(range(n)) or any(
                sum(edges[k][2][i] for k in chosen)%3!=t for i,t in enumerate(target)):
            raise AssertionError("extracted witness failed source replay")
        return "SAT",tuple(chosen)
    return "UNKNOWN",None
