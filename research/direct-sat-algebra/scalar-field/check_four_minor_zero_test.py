"""Exhaust the named Grassmannian and check the extension projection with private rows."""
from itertools import combinations
from random import Random
from punctured_witness import BinaryField
from quadratic_centroid import independent

f=BinaryField(19)
ports=((1,0),(2,0),(0,1),(4,8))


def project(x):
    u=v=0
    for i,(a,b) in enumerate(ports):
        if x>>i&1:
            u^=a
            v^=b
    return u,v


def rank(cols):
    rows={}
    for v in cols:
        v=list(v)
        for k in sorted(rows):
            c=v[k]
            v=[a^f.mul(c,b) for a,b in zip(v,rows[k])]
        idx=next((i for i,x in enumerate(v) if x),None)
        if idx is not None:
            inv=f.inverse(v[idx])
            rows[idx]=[f.mul(inv,t) for t in v]
    return len(rows)


def main():
    planes={tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,16),2)}
    assert len(planes)==35
    assert [p for p in planes if rank(map(project,p))<2]==[(1,2,3)]
    rng=Random(944)
    for r in range(4):
        for _ in range(300):
            B=[rng.randrange(1<<(r+4)) for _ in range(r+2)]
            priv=[x>>4 for x in B]
            basis1=len(independent([((x>>4)<<2)|(x&3) for x in B]))==r+2
            nonbasis2=rank([tuple((a>>j)&1 for j in range(r))+project(x)
                            for x,a in zip(B,priv)])<r+2
            space={0}
            for x in B:
                space|={z^x for z in space}
            good=(len(independent(priv))==r and {x for x in space if x<16}=={0,1,2,3})
            assert good==(basis1 and nonbasis2)
    print("35 trace planes and 1200 private-row candidate bases verified")


if __name__=="__main__":
    main()
