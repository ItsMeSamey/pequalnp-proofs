"""Bounded direct-seed and complete dual-subspace lattice audit."""
from functools import lru_cache
from itertools import combinations
from quadratic_polar_online import Quadratic, count_histogram, discover_anchor


def pairmask(i,j):
    assert i<j
    return 1 << (j*(j-1)//2+i)


def value(q,s):
    answer=q.constant ^ ((q.linear & s).bit_count()%2)
    for j in range(s.bit_length()):
        if s>>j&1:
            for i in range(j):
                if s>>i&1 and q.pairs & pairmask(i,j):
                    answer ^= 1
    return answer


def polar(q,x,y):
    return value(q,x^y)^value(q,x)^value(q,y)^value(q,0)


def span(items):
    found={0}
    for u in items:
        found |= {z^u for z in tuple(found)}
    return frozenset(found)


def basis(items):
    independent=[]
    found={0}
    for u in sorted(items):
        if u not in found:
            independent.append(u)
            found |= {z^u for z in tuple(found)}
    return tuple(independent)


@lru_cache(None)
def lattice(h,k):
    spaces={frozenset({0})}
    for _ in range(min(h,k)):
        grown=set(spaces)
        for W in spaces:
            for u in range(1,1<<h):
                if u not in W:
                    grown.add(W | {z^u for z in W})
        spaces=grown
    return tuple(spaces)


@lru_cache(None)
def kernel_basis(h,W):
    return basis(x for x in range(1<<h) if all((x&w).bit_count()%2==0 for w in W))


@lru_cache(None)
def restriction(h,pairs,W):
    dirs=kernel_basis(h,W)
    q=Quadratic(0,0,pairs)
    return sum(polar(q,dirs[i],dirs[j])*pairmask(i,j)
               for i,j in combinations(range(len(dirs)),2))


def dimension(h,W,qs):
    return len(basis(restriction(h,q.pairs,W) for q in qs))


def rank(h,q):
    return len(basis(sum(polar(q,1<<i,1<<j)<<j for j in range(h)) for i in range(h)))


def discovery(h,k,r,qs):
    valid={W for W in lattice(h,k) if dimension(h,W,qs)<=r}
    got=discover_anchor(h,k,r,tuple(qs))
    if valid:
        assert got is not None and len(got)<=k and len(span(got))==1<<len(got)
        assert span(got) in valid
    else:
        assert got is None
    return valid


def direct(h,stored,current):
    ans=[0,0]
    for s in range(1<<h):
        if all(value(q,s)==bit for q,bit in stored):
            ans[value(current,s)]+=1
    return tuple(ans)


def count(h,k,r,stored,current,possible=True):
    got=count_histogram(h,k,r,tuple(stored),current)
    if possible:
        assert got==direct(h,stored,current),(stored,current,got)
    else:
        assert got is None
    return got


def product(a,b,linear=0,constant=0,extra=0):
    pairs=extra
    for i,j in combinations(range(max(a,b).bit_length()),2):
        if ((a>>i&1)*(b>>j&1)) ^ ((a>>j&1)*(b>>i&1)):
            pairs ^= pairmask(i,j)
    return Quadratic(constant,linear^(a&b),pairs)


def lattice_suite():
    qs=[Quadratic(i%2,(3*i)%8,i) for i in range(1,8)]
    checks=0
    for sel in range(1<<len(qs)):
        chosen=[q for j,q in enumerate(qs) if sel>>j&1]
        for k,r in ((0,0),(0,1),(1,0),(1,1),(2,0)):
            good=discovery(3,k,r,chosen)
            if sel%17==0:
                equations=[(q,value(q,5)) for q in chosen]
                count(3,k,r,equations,Quadratic(1,7,5),bool(good))
            checks+=1
    return checks


def count_controls():
    zero=Quadratic(0,0,0)
    one=Quadratic(1,0,0)
    assert count(0,0,0,[],one)==(0,1)
    assert count(0,0,0,[(zero,1)],one)==(0,0)
    assert count(4,0,0,[(Quadratic(1,3,0),0)],Quadratic(1,3,0))==(8,0)

    # (x0+1)(x1+1) + x2*x3 + x4. A free linear radical term balances the sum.
    q=Quadratic(1,19,pairmask(0,1)|pairmask(2,3))
    assert rank(5,q)==4 and count(5,0,0,[],q)==(16,16)
    x4=Quadratic(0,16,0)
    assert count(5,0,0,[(x4,0)],q)==(10,6)
    assert count(5,0,0,[(x4,1)],q)==(6,10)
    assert count(5,0,1,[(q,0),(q,1)],x4)==(0,0)
    shifted=Quadratic(0,q.linear,q.pairs)
    assert count(5,0,1,[(q,1),(shifted,1)],x4)==(0,0)

    # Only one nonzero member of this pencil can vanish on a hyperplane.
    high=Quadratic(1,9,pairmask(0,1)|pairmask(2,3))
    low=Quadratic(0,5,pairmask(0,2))
    other=Quadratic(1,12,high.pairs^low.pairs)
    assert [rank(4,f) for f in (high,low,other)]==[4,2,4]
    for qs in ((high,low),(other,high),(low,other)):
        assert discovery(4,1,1,qs)=={span((w,)) for w in (1,4,5)}
        count(4,1,1,[(f,value(f,11)) for f in qs],Quadratic(0,7,31))
    assert not discovery(4,1,0,(high,))
    count(4,1,0,[(high,0)],low,False)
    trio=[Quadratic(0,0,pairmask(i,j)) for i,j in combinations(range(3),2)]
    assert not discovery(3,1,0,trio)
    count(3,1,0,[(f,0) for f in trio],zero,False)


def combined_family():
    # A coordinate change t=x0+x1 hides the unique working line.
    h=7
    R=pairmask(3,4)|pairmask(5,6)
    qs=[Quadratic(1,71,R),product(3,2,21,0,R),product(3,4,102,1,R)]
    assert [rank(h,f) for f in qs]==[4,6,6]
    assert discovery(h,1,1,qs)=={span((3,))}
    for seed in (0,39,82,127):
        stored=[(f,value(f,seed)) for f in qs]
        current=Quadratic(1,37,pairmask(0,5)|pairmask(1,6)|pairmask(2,4))
        count(h,1,1,stored,current)


def online():
    # Online reconstruction from the public counting API; the fresh query does
    # not enter the anchor search until after a genuinely wrong prediction.
    totals=[]
    for secret in range(16):
        K=pairmask(2,3)
        stored=[]
        rounds=[]
        if secret==15:
            rounds.extend(Quadratic(0,1<<i,0) for i in range(4))
        rounds.extend(product(3,a,(a*7)%16,a%2,K if a%3 else 0) for a in range(16))
        previous=0
        for index,base in enumerate(rounds):
            if secret==15 and index<4:
                f=base
            else:
                f=Quadratic(base.constant^previous,base.linear,base.pairs)
            a,b=count(4,1,1,stored,f)
            truth=value(f,secret)
            if int(b>a)!=truth:
                stored.append((f,truth))
                remaining=sum(all(value(q,s)==v for q,v in stored) for s in range(16))
                assert 0<2*remaining<=a+b
                assert len(stored)<=4
            previous=truth
        if secret==15:
            assert len(stored)==4
        totals.append(len(stored))
    return tuple(totals)


if __name__=='__main__':
    print('complete lattice comparisons',lattice_suite())
    count_controls()
    combined_family()
    print('mistakes by original seed',online())
