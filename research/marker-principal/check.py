from random import Random
def odd(x):return x.bit_count()%2
def fullrank(rows):
    piv={}
    for v in rows:
        while v:
            k=v.bit_length()
            if k not in piv:
                piv[k]=v
                break
            v^=piv[k]
        else:return False
    return True
def check(A,h):
    n=len(A)
    markers=set()
    for S in range(1,1<<n):
        I=[i for i in range(n) if S>>i&1]
        P=[A[i]&S for i in I]
        if fullrank(P):continue
        for j in range(len(P)):
            R=P[:]
            R[j]^=h&S
            if fullrank(R):markers.add(S);break
    answers=[s for s in range(1<<n) if odd(h&s) and all(not(s>>i&1) or not odd(a&s) for i,a in enumerate(A))]
    assert bool(markers)==bool(answers)
    if answers:assert min(answers,key=int.bit_count) in markers
rng=Random(712)
for n in range(1,4):
    for code in range(1<<(n*n)):
        A=[(code>>(i*n))% (1<<n) for i in range(n)]
        for h in range(1<<n):check(A,h)
for i in range(300):
    n=rng.randrange(4,9)
    check([rng.randrange(1<<n) for j in range(n)],rng.randrange(1<<n))
print('4164 exhaustive pairs and 300 random pairs passed')
