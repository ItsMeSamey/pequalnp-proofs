from random import Random
from collections import Counter
rng=Random(76)
def rank(rows):
    piv={}
    for v in rows:
        while v:
            j=v.bit_length()-1
            if j in piv:v ^= piv[j]
            else:
                piv[j]=v
                break
    return len(piv)
def polar(T,n,s):
    return [sum((((T[0]^T[1<<i]^T[1<<j]^T[(1<<i)^(1<<j)])&s).bit_count()%2)<<j for j in range(n)) for i in range(n)]
def transform(T,n):
    while True:
        B=[rng.randrange(1<<n) for _ in range(n)]
        if rank(B)==n:break
    p=[rng.randrange(1<<n)]
    for u in B:p += [x^u for x in p]
    return [T[x] for x in p]
def mul(x,y):
    a=0
    while y:
        if y&1:a ^= x
        y>>=1; x<<=1
        if x&4:x ^= 7
    return a
T=[mul(x&3,x>>2) for x in range(16)]
assert sorted(Counter(T).values())==[3,3,3,7]
for _ in range(100):
    V=transform(T,4)
    assert all(rank(polar(V,4,s))==4 for s in (1,2,3)) and set(V)==set(range(4))
T=[]
for x in range(64):
    a,b,c=[(x>>(2*i)&3)==3 for i in range(3)]
    T.append((a^c)+2*(b^c))
for _ in range(60):
    V=transform(T,6)
    P,Q=[polar(V,6,s) for s in (1,2)]
    assert all(rank(polar(V,6,s))==4 for s in (1,2,3)) and set(V)==set(range(4))
    K=[x for x in range(64) if all((v&x).bit_count()%2==0 for v in P)]
    L=[x for x in range(64) if all(sum(((x>>i)&1)*(v&k).bit_count() for i,v in enumerate(M))%2==0 for k in K for M in (P,Q))]
    assert len(K)==4 and len(L)==16 and set(K)&set(L)=={0}
print('160 hidden-basis checks passed')
