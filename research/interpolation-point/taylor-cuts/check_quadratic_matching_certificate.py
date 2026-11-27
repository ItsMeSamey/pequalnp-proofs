from itertools import product,permutations
from random import Random
from quadratic_matching_certificate import certificate,verify


def inflate(k):
    stride=2*k+1
    size=6*stride
    edges=[]
    for g in range(6):
        start=g*stride
        for u in range(k+1):
            for v in range(k):
                edges.append((start+u,start+k+1+v,(0,)))
    for i,j,u,v in product(range(3),range(3),range(k+1),range(k+1)):
        edges.append((i*stride+u,(3+j)*stride+v,((i*j)%3,)))
    return size,edges


if __name__=="__main__":
    rng=Random(637)
    for _ in range(100):
        n=rng.randrange(1,5)
        b=rng.randrange(3)
        labels={(u,v):tuple(rng.randrange(3) for _ in range(b))
                for u,v in product(range(n),repeat=2) if rng.randrange(5)}
        t=tuple(rng.randrange(3) for _ in range(b))
        actual=any(all((i,p[i]) in labels for i in range(n))
                   and all(sum(labels[i,p[i]][j] for i in range(n))%3==t[j] for j in range(b))
                   for p in permutations(range(n)))
        e=[(i,n+j,g) for (i,j),g in labels.items()]
        proof=certificate(2*n,e,t,extension_conflicts=True)
        if proof is not None:
            assert not actual and verify(2*n,e,t,proof)
    for k in (0,1):
        n,e=inflate(k)
        proof=certificate(n,e,(0,),extension_conflicts=True)
        assert proof and verify(n,e,(0,),proof)
        assert not verify(n,e,(1,),proof)
        assert not verify(n,e,(0,),{**proof,("unverified",):1})
        print("inflation",k,"vertices",n,"edge choices",len(e),"certificate rows",len(proof))
    print("100 brute-force soundness controls passed")
