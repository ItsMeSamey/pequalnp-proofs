"""Check each score recurrence on represented binary spaces, including free-bit cases."""
from random import Random

def orthogonal(space,n):
    return {y for y in range(1<<n) if all(not ((y&x).bit_count()%2) for x in space)}

def score(v,labels):
    x=0
    for i,a in enumerate(labels):
        if v>>i&1:x^=a
    return x

def image(Z,Zd,A,B):
    return {score(c,A)^score(d,B) for c in Z for d in Zd if not c&d}

def check(n,Z,A,B):
    Zd=orthogonal(Z,n); bit=1<<(n-1); mask=bit-1
    target=image(Z,Zd,A,B)
    eA,eB=A[-1],B[-1]; A=A[:-1];B=B[:-1]
    trC=next((x for x in Z if x&bit),None); trD=next((y for y in Zd if y&bit),None)
    if trC is None or trD is None:
        small=image({z&mask for z in Z},{d&mask for d in Zd},A,B)
        free=eB if trC is None else eA
        assert target==small|{h^free for h in small}
        return
    A2=[a^(eA if trD>>i&1 else 0) for i,a in enumerate(A)]
    B2=[b^(eB if trC>>i&1 else 0) for i,b in enumerate(B)]
    deletion=image({z for z in Z if not z&bit},{d&mask for d in Zd},A,B2)
    contraction=image({z&mask for z in Z},{d for d in Zd if not d&bit},A2,B)
    assert deletion|contraction==target

rng=Random(12)
for i in range(600):
    n=1+i%8; Z={0}
    for _ in range(rng.randrange(n+1)):
        v=rng.randrange(1<<n); Z|={z^v for z in Z}
    check(n,Z,[rng.randrange(8) for _ in range(n)],[rng.randrange(8) for _ in range(n)])
print("Verified deletion/contraction score images on 600 binary-matroid instances.")
