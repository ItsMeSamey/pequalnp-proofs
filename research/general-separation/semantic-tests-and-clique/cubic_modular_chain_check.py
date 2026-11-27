"""Finite projective-orbit, physical chain, and modular sign-sum controls."""
from collections import deque
from itertools import product
from math import isqrt


def step(e,v):
    a,b=v
    return ((4 if e==0 else 2)*(a+b),(2 if e==0 else 4)*(b-a))


def weights(word):
    v=(4,-2)
    for e in word:v=step(e,v)
    return v


def key(v,p):
    a,b=v
    if b%p:return a*pow(b,-1,p)%p
    assert a%p
    return p


def search(p):
    initial=key((4,-2),p)
    queue=deque([initial])
    parent={initial:None}
    while queue:
        t=queue.popleft()
        if t==1:break
        v=(1,0) if t==p else (t,1)
        for e in (0,1):
            s=key(step(e,v),p)
            if s not in parent:
                parent[s]=(t,e)
                queue.append(s)
    if 1 not in parent:raise ValueError(('target unreachable',p))
    t=1
    word=[]
    while parent[t] is not None:
        t,e=parent[t]
        word.append(e)
    word.reverse()
    assert len(word)<=p
    a,b=weights(word)
    assert a%p==b%p!=0
    return word


def physical(word):
    eps=list(reversed(word))+[0]
    L=len(eps)
    total=[0,0]
    for w in range(1<<(3*L)):
        parity=0
        for j,e in enumerate(eps):
            u,a,b=[(w>>(3*j+k))&1 for k in range(3)]
            parity^=(u^e)&a&b
            parity^=u
            if j:parity^=u&(w>>(3*j-3)&1)
        total[w&1]+=(-1)**parity
    return tuple(total)


def crt_update(x,M,y,p):
    return x+M*((y-x)*pow(M,-1,p)%p),M*p


if __name__=='__main__':
    for k in range(4):
        for word in product((0,1),repeat=k):assert physical(word)==weights(word)
    primes=[p for p in range(3,252,2) if all(p%d for d in range(3,isqrt(p)+1))]
    distances={p:len(search(p)) for p in primes}
    print(len(primes),'primes; largest shortest word',max(distances.values()),
          'for', [p for p,k in distances.items() if k==max(distances.values())])
    # Known six-source drift with negative sign sum; directly weight its rows.
    n=6
    def sign(x):return -(-1)**(((x&7)==7)^((x&24)==24)^((x&35)==35))
    exact=sum(sign(x) for x in range(1<<n))
    x=M=1
    for p in primes:
        a,b=weights(search(p))
        Z=sum(sign(z)*a**(n-z.bit_count())*b**z.bit_count() for z in range(1<<n))
        residue=Z*pow(pow(a,n,p),-1,p)%p
        x,M=crt_update(x,M,residue,p)
        assert x%M==exact%M
        if M>2*(1<<n):break
    assert (x if 2*x<M else x-M)==exact
    print('15 raw phase words; CRT modulus',M,'signed sum',exact)
