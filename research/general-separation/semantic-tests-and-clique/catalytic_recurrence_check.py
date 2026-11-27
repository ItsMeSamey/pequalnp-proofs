"""Compare GF(2) recurrence coefficients to Cartier steps and dirty shears."""
from random import Random

def step(v,q,b,w):
    prod=0
    for j in range(w):
        if v>>j&1:
            prod ^= q<<j
    return sum(((prod>>(2*j+b))&1)<<j for j in range(w))

def direct(p,q,t,w):
    values=[]
    for i in range(t+1):
        a=(p>>i)&1
        for j in range(1,min(w,i)+1):
            a ^= ((q>>j)&1)*values[i-j]
        values.append(a)
    return values[-1]

def shear(reg,l,r,q,bits,w):
    if r==l+1:
        reg[r]^=step(reg[l],q,bits[l],w)
    else:
        m=(l+r)//2
        for _ in range(2):
            shear(reg,l,m,q,bits,w)
            shear(reg,m,r,q,bits,w)

rng=Random(619)
count=0
for w in range(1,9):
    for _ in range(120):
        q=1|(rng.randrange(1<<w)<<1)
        p=rng.randrange(1<<w)
        t=rng.choice([0,1,rng.randrange(256)])
        bits=[(t>>i)&1 for i in range(t.bit_length()+rng.randrange(4))]
        v=p
        for b in bits:
            v=step(v,q,b,w)
        assert v&1 == direct(p,q,t,w)
        reg=[p]+[rng.randrange(1<<w) for b in bits]
        before=reg.copy()
        if bits:
            shear(reg,0,len(bits),q,bits,w)
            before[-1]^=v
        assert reg==before
        count+=1
print(count,'recurrences with explicit coefficients, zero padding and dirty product checks passed')
