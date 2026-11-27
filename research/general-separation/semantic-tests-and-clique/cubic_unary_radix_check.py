"""Independent chain sign sums and balanced radix recovery."""
from math import gcd,comb
from random import Random


def weights(L):
    A,B=2,1
    for _ in range(1,L):
        A,B=2*(A+B),A-B
    assert gcd(A,B)==1
    return A,B


def raw_chain(L,source):
    total=0
    for rest in range(1<<(3*L-1)):
        state=(rest<<1)|source
        uv=state&((1<<L)-1)
        av=(state>>L)&((1<<L)-1)
        bv=state>>(2*L)
        parity=((uv&av&bv).bit_count()+(uv&(uv>>1)).bit_count())%2
        total+=(-1)**parity
    return total


def recover(z,n,A,B):
    out=[0]*(n+1)
    for j in range(n,-1,-1):
        residue=z*pow(pow(B,j,A),-1,A)%A
        if 2*residue>A:residue-=A
        out[j]=residue
        z,rem=divmod(z-residue*B**j,A)
        assert rem==0
    assert z==0
    return out


def check(n,phase,L):
    A,B=weights(L)
    hist=[0]*(n+1)
    z=0
    for x in range(1<<n):
        sign=(-1)**(sum(x&t==t for t in phase)%2)
        j=x.bit_count()
        hist[j]+=sign
        z+=sign*A**(n-j)*B**j
    assert A>2*max(comb(n,j) for j in range(n+1))
    assert recover(z,n,A,B)==hist
    return sum(hist),hist


def circuit_case():
    # Two gates c=ab, d=c XOR a; Fourier bit s or t per equality and d=1 pin.
    n=6
    a,b,c,d,s,t=[1<<i for i in range(n)]
    p={s|c,s|a|b,t|d,t|c,t|a}
    # Add the output pin by replacing d with 1 and removing that variable.
    p.remove(t|d)
    p.add(t)
    # Renumber remaining five sources continuously.
    p={((m&7)|((m>>1)&~7)) for m in p}
    S,hist=check(5,p,6)
    assert S==4*sum((a^a*b) for a in range(2) for b in range(2))
    return hist


if __name__=='__main__':
    for L in range(1,4):
        actual=tuple(raw_chain(L,s) for s in (0,1))
        assert actual==tuple((1<<L)*x for x in weights(L))
        print('L',L,'conditional weights',actual)
    # Enumerate a complete two-chain graph with logical drift xy+x.
    L=2
    A,B=weights(L)
    total=0
    for w in range(1<<(6*L)):
        parity=0
        for j in range(2):
            u,a,b=[(w>>(3*L*j+i*L))&((1<<L)-1) for i in range(3)]
            parity+=(u&a&b).bit_count()+(u&(u>>1)).bit_count()
        x,y=w&1,(w>>(3*L))&1
        total+=(-1)**((parity+x*y+x)%2)
    z,rem=divmod(total,1<<(2*L))
    assert rem==0 and recover(z,2,A,B)==[1,0,1]
    rng=Random(928)
    negative=0
    for n in range(1,8):
        for i in range(12):
            p={m for m in range(1<<n) if m.bit_count()<=3 and rng.randrange(2)}
            _,hist=check(n,p,8)
            negative+=any(c<0 for c in hist)
    assert negative>0
    print('84 random drifts;',negative,'with negative coefficients; circuit Fourier histogram',circuit_case())
