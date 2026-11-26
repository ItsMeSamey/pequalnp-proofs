"""Compare full affine-equation spaces, in original coordinates."""
import argparse
from hull import add, normalize, restrictions, pc


def annihilator(points, width):
    rows={}
    for p in points:
        add(rows,p)
    result={}
    for k in range(width):
        if k+1 in rows:
            continue
        h=1<<k
        for p,v in sorted(rows.items()):
            if (h&v).bit_count()%2:
                h ^= 1<<(p-1)
        add(result,h)
    return result


def compare(adj):
    n=len(adj)
    if n<2 or not(adj[0]&2 and adj[1]&1):
        raise ValueError("vertices 0 and 1 must be adjacent")
    if any(a<0 or a>>n or a>>i&1 or any((a>>j&1)!=(adj[j]>>i&1) for j in range(n))
           for i,a in enumerate(adj)):
        raise ValueError("expected simple undirected adjacency masks")
    normalized=normalize(adj)
    points=[(x<<1)|1 for x in range(3,1<<n,4)
            if all(not(x>>i&1) or not((x&a).bit_count()%2) for i,a in enumerate(adj))]
    exact=annihilator(points,n+1)
    if normalized is None:
        algebraic=[{j+1:1<<j for j in range(n+1)} for _ in (2,3)]
    else:
        forms,vertices=normalized
        def lift(h):
            return (h&1)|sum(((h>>(j+1))&1)<<(v+1) for j,v in enumerate(vertices))
        pins={}
        for i,f in enumerate(forms):
            add(pins,lift(f)^(1<<(i+1)))
        guards=restrictions(adj,forms)
        algebraic=[]
        for d in (2,3):
            eq=pins.copy()
            for f in pc(guards,len(vertices),d).values():
                add(eq,lift(f))
            algebraic.append(eq)
    return points,exact,*algebraic


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("adj",nargs="+",type=int)
    args=parser.parse_args()
    points,exact,q,c=compare(args.adj)
    print("Support masks:",[p>>1 for p in points])
    print("Affine form bit 0 is the constant and bit i+1 is the coefficient of vertex i.")
    for name,basis in (("Oracle",exact),("Degree 2",q),("Degree 3",c)):
        print(name,"basis:",sorted(basis.values()))
    for name,basis in (("Degree 2",q),("Degree 3",c)):
        ext=basis.copy()
        missing=[p for p in exact.values() if add(ext,p)]
        print(name,"missing independent forms:",missing)
