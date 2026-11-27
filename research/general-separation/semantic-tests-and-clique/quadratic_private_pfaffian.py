"""Mixed Pfaffian parity on a supplied 2r-coordinate bag over GF(2)."""
from itertools import combinations
from random import Random


def nonsingular(rows):
    pivots={}
    for col in rows:
        while col:
            i=col.bit_length()-1
            if i not in pivots:
                pivots[i]=col
                break
            col^=pivots[i]
        if not col:return 0
    return 1


def mixed_parity(forms,bag):
    r=len(forms)
    if len(bag)!=2*r or len(set(bag))!=2*r or any(i<0 for i in bag):
        raise ValueError('bag requires 2r distinct coordinates')
    matrices=[]
    for form in forms:
        if any(t<0 or t.bit_count()>2 for t in form):raise ValueError('quadratic required')
        rows=[0]*(2*r)
        for i,j in combinations(range(2*r),2):
            if ((1<<bag[i])|(1<<bag[j])) in form:
                rows[i]^=1<<j
                rows[j]^=1<<i
        matrices.append(rows)
    total=0
    rows=[0]*(2*r)
    for k in range(1<<r):
        if k:
            changed=(k&-k).bit_length()-1
            rows=[a^b for a,b in zip(rows,matrices[changed])]
        total^=nonsingular(rows)
    return total


def tests():
    rng=Random(972)
    def check(forms,n,bag):
        ans=mixed_parity(forms,bag)
        other=[j for j in range(n) if j not in bag]
        counts=[]
        for fixed in range(1<<len(other)):
            offset=sum((1<<j) for k,j in enumerate(other) if fixed>>k&1)
            hist=[0]*(1<<len(forms))
            for u in range(1<<len(bag)):
                x=offset|sum(1<<j for k,j in enumerate(bag) if u>>k&1)
                y=sum((sum(x&t==t for t in p)%2)<<i for i,p in enumerate(forms))
                hist[y]+=1
            assert all(c%2==ans for c in hist)
            counts.append(hist)
        return ans,counts
    disjoint=[{3},{12},{48}]
    assert check(disjoint,6,list(range(6)))==(1,[[27,9,9,3,9,3,3,1]])
    # F4 multiplication on two 2-bit operands, modulus X^2+X+1.
    f4=[{5,10},{6,9,10}]
    assert check(f4,4,list(range(4)))==(1,[[7,3,3,3]])
    switch=[{3},{5,4}]
    assert check(switch,4,list(range(4)))==(0,[[8,4,4,0]])
    # Two outside coordinates have arbitrary affine effects after pinning.
    for _ in range(80):
        r=rng.choice([2,3])
        n=2*r+2
        bag=rng.sample(range(n),2*r)
        p=[{(1<<i)|(1<<j) for i,j in combinations(range(n),2) if rng.randrange(2)} for _ in range(r)]
        ans,_=check(p,n,bag)
        for s in p:
            s.update(t for t in [0]+[1<<i for i in range(n)] if rng.randrange(2))
        assert check(p,n,bag)[0]==ans
    planted=[{(1<<1)|(1<<4)}, {(1<<2)|(1<<5)}]
    bags=[bag for bag in combinations(range(6),4) if mixed_parity(planted,bag)]
    assert bags==[(1,2,4,5)]
    print('80 random before/after perturbations, three fiber controls and unique hidden minor passed')


if __name__=='__main__':tests()
