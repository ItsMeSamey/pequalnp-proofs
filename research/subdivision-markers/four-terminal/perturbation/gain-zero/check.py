"""Compare the structural and switched-score tests with original matrix ranks."""
from itertools import combinations
from random import Random


def rank(cols):
    piv={}
    for x in cols:
        while x:
            j=x.bit_length()-1
            if j not in piv:
                piv[j]=x
                break
            x^=piv[j]
    return len(piv)


def par(x):
    return x.bit_count()&1


def inspect(n,edges,settings):
    B=[(1<<a)^(1<<b) for a,b in edges]
    shape={}
    for mask in range(1,1<<len(edges)):
        used=[i for i in range(len(edges)) if mask>>i&1]
        boundary=0
        for i in used:
            boundary^=B[i]
        if boundary:
            continue
        nullity=len(used)-rank([B[i] for i in used])
        vertices=sum(1<<v for v in {v for i in used for v in edges[i]})
        shape[mask]=(used,nullity,vertices)
    checks=0
    positive=0
    for d,gamma,q in settings:
        gp=gamma^sum(par(q&b)<<i for i,b in enumerate(B))
        A=[b^(d if gamma>>i&1 else 0) for i,b in enumerate(B)]
        cover=min(z.bit_count() for z in range(1<<n) if all(
            not(gp>>i&1) or z>>a&1 or z>>b&1 for i,(a,b) in enumerate(edges)))
        for mask,(used,beta,verts) in shape.items():
            if par(gamma&mask):
                continue
            truth=rank([A[i] for i in used])==len(used)-1
            predicted=False
            if beta==1:
                assert (gp&mask).bit_count()<=2*cover
                spin=next(p for p in range(1<<n) if all(par(p&B[i])==((gp>>i)&1) for i in used))
                score=0
                for i in used:
                    a,b=edges[i]
                    da,db=(d>>a)&1,(d>>b)&1
                    pa,pb=(spin>>a)&1,(spin>>b)&1
                    if gp>>i&1:
                        assert pa!=pb
                        score+=da*pa+db*pb
                    else:
                        assert pa==pb
                        score+=pa*(da+db)
                assert score%4==2*par(spin&d&verts)
                predicted=bool(d&~verts) or bool(par(d)) or score%4==2*par(q&d)
            if beta==2:
                small=[x for x in shape if x&mask==x and shape[x][1]==1]
                pairs=[(a,b) for a,b in combinations(small,2) if a^b==mask and not a&b]
                assert pairs
                a,b=pairs[0]
                va,vb=shape[a][2],shape[b][2]
                assert (va&vb).bit_count()<=1
                scores=[]
                for x in (a,b):
                    scores.append(sum(((d>>v)&1) for i in shape[x][0] for v in edges[i])%4)
                if va&vb:
                    component_odd=(sum(scores)-2*par(d&va&vb))%4==2
                else:
                    component_odd=(2 in scores)
                predicted=bool(par(gamma&a) and par(gamma&b) and (d&~verts or component_odd))
            assert predicted==truth,(n,edges,d,gamma,q,mask,truth,predicted)
            checks+=1
            positive+=truth
    return checks,positive


if __name__=='__main__':
    rng=Random(6871)
    totals=[0,0]
    graphs=[(4,list(combinations(range(4),2))),
            (3,[(0,0),(0,1),(0,1),(1,1),(1,2),(2,0)]),
            (4,[(0,0),(0,1),(0,1),(2,2),(2,3),(2,3)])]
    for n,edges in graphs:
        cases=((d,g,rng.randrange(1<<n)) for d in range(1,1<<n) for g in range(1<<len(edges)))
        checks=inspect(n,edges,cases)
        totals=[a+b for a,b in zip(totals,checks)]
    for _ in range(160):
        n=rng.randrange(2,7)
        edges=[(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(1,9))]
        cases=[(rng.randrange(1,1<<n),rng.randrange(1<<len(edges)),rng.randrange(1<<n)) for _ in range(12)]
        totals=[a+b for a,b in zip(totals,inspect(n,edges,cases))]
    print(*totals,'candidate/switch comparisons and true circuits')
