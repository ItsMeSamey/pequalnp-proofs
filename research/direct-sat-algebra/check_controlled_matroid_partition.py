"""Independent small exhaustive checks and a mixed-rank strict improvement."""
import random
from itertools import product
from controlled_matroid_partition import exact, partition


def rank(cols):
    s={0}
    for v in cols:
        s.update([w^v for w in s])
    return len(s).bit_length()-1


def check(U,V,s,t):
    k=len(U)
    S,T,I,r=partition(U,V,s,t)
    assert set(S)|set(T)==set(range(k)) and not set(S)&set(T)
    opt=min(rank(U[i] for i in range(k) if mask>>i&1)+rank(V[i] for i in range(k) if not mask>>i&1)
            for mask in range(1<<k) if all(mask>>i&1 for i in s) and all(not mask>>i&1 for i in t))
    assert opt==sum(r)
    for cols,forced in [(U,s),(V,t)]:
        assert rank(cols[i] for i in (*forced,*I))==rank(cols[i] for i in forced)+len(I)


def main():
    for word in product(range(4),repeat=4):
        check(word[:2],word[2:],(),())
    rng=random.Random(941)
    misses=0
    for _ in range(800):
        k,n,m=[rng.randrange(v) for v in (8,5,5)]
        U=[rng.randrange(1<<m) for i in range(k)]
        V=[rng.randrange(1<<n) for i in range(k)]
        q=[(v,rng.randrange(2)) for v in V]
        rhs=[rng.randrange(1<<m) for i in range(n)]
        b=rng.randrange(1<<m)
        picks=[rng.randrange(4) for i in range(k)]
        s=[i for i,p in enumerate(picks) if p==1]
        t=[i for i,p in enumerate(picks) if p==2]
        check(U,V,s,t)
        eq=[(rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(3))]
        valid=set()
        for y in range(1<<n):
            if any((y&v).bit_count()%2!=c for v,c in eq):
                continue
            target=b
            for j,v in enumerate(rhs):
                if y>>j&1:
                    target^=v
            for x in range(1<<k):
                z=0
                for j,(v,c) in enumerate(q):
                    if x>>j&1 and ((v&y).bit_count()%2)^c:
                        z^=U[j]
                if z==target:
                    valid.add((x,y))
        cnt,w,info=exact(m,rhs,b,U,q,equations=eq,force_s=s,force_t=t)
        assert cnt==len(valid) and (w in valid if cnt else w is None)
        if info.get('ranks') and sum(info['ranks']):
            cnt,w,meta=exact(m,rhs,b,U,q,equations=eq,force_s=s,force_t=t,budget=sum(info['ranks'])-1)
            assert cnt is None and w is None and meta['status']=='budget'
            misses+=1
    U=[1]*9+[1<<i for i in range(1,10)]
    V=[1<<i for i in range(1,10)]+[1]*9
    assert partition(U,V)[-1]==(1,1) and rank(U)==rank(V)==10
    print('256 exhaustive pairs, 800 forced rank/count/witness trials,',misses,'budget misses, strict 2 versus 10 passed')


if __name__=='__main__':
    main()
