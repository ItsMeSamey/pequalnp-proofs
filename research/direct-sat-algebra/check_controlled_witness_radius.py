"""Independent enumerative controls for projected counts, y-pinning, and radius search."""
from collections import Counter
from itertools import product
from random import Random
from controlled_witness_radius import ProjectedOracle, column_basis, search


def dot(a,b):
    return (a&b).bit_count()%2


def linear(A,y):
    result = 0
    for j,u in enumerate(A):
        if y>>j&1:
            result ^= u
    return result


def span_size(U):
    return (len({linear(U,x) for x in range(1<<len(U))})).bit_length()-1


def run(m,A,b,U,q,I,flat,stats):
    n,k=len(A),len(U)
    R=span_size(U)
    left=[i for i in range(k) if i not in I]
    overlap=len(I)+span_size([U[i] for i in left])-R
    valid=[]
    counts=Counter()
    for y in range(1<<n):
        if any(dot(mask,y)!=rhs for mask,rhs in flat):
            continue
        active=sum((dot(mask,y)^c)<<i for i,(mask,c) in enumerate(q))
        for x in range(1<<k):
            if linear(U,x&active)==linear(A,y)^b:
                valid.append((x,y))
                missing=tuple(i for i in I if not active>>i&1)
                counts[missing,y]+=1
    for pattern in product((0,1),repeat=len(I)):
        M=tuple(i for i,p in zip(I,pattern) if not p)
        active_basis=column_basis(U[i] for i,p in zip(I,pattern) if p)
        eq=flat+[(q[i][0],q[i][1]^p) for i,p in zip(I,pattern)]
        oracle=ProjectedOracle(m,A,b,[U[i] for i in left],[q[i] for i in left],active_basis,eq)
        # Every projected completion has exactly 2^|M| original control completions.
        for mask in range(1<<n):
            for rhs in (0,1):
                exact=sum(counts[M,y] for y in range(1<<n) if dot(mask,y)==rhs)
                assert oracle.count([(mask,rhs)])*(1<<len(M))==exact
                stats['pinned counts']+=1
    normalized=len(valid)//(1<<(k-R))
    assert len(valid)==normalized*(1<<(k-R))
    for p in (1,2,len(I)+2):
        ans=search(m,A,b,U,q,p,I,flat)
        in_radius=any(num and len(M)<overlap+p for (M,y),num in counts.items())
        assert (ans is not None)==in_radius
        if ans is None:
            assert normalized%(1<<p)==0
            if valid: stats['SAT misses']+=1
        else:
            assert ans in valid
        stats['searches']+=1
    stats['cases']+=1


def main():
    stats=Counter()
    for a,b,u0,u1,mask0,c0,mask1,c1 in product((0,1),repeat=8):
        for I in ([],[0],[1]):
            if any(not [u0,u1][i] for i in I): continue
            run(1,[a],b,[u0,u1],[(mask0,c0),(mask1,c1)],I,[],stats)
    run(0,[],0,[],[],[],[],stats)
    rng=Random(92013)
    for _ in range(250):
        m,n,k=[rng.randrange(5) for _ in range(3)]
        A=[rng.randrange(1<<m) for _ in range(n)]
        U=[rng.randrange(1<<m) for _ in range(k)]
        b=rng.randrange(1<<m)
        q=[(rng.randrange(1<<n),rng.randrange(2)) for _ in U]
        flat=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
        I=[]
        for i in rng.sample(range(k),k):
            if rng.randrange(2) and span_size([U[j] for j in I+[i]])>len(I):
                I.append(i)
        run(m,A,b,U,q,I,flat,stats)
        default=search(m,A,b,U,q,k+1,equations=flat)
        assert (default is not None)==bool(any(
            all(dot(mask,y)==rhs for mask,rhs in flat) and
            any(linear(U,x&sum((dot(mask,y)^c)<<i for i,(mask,c) in enumerate(q)))==linear(A,y)^b
                for x in range(1<<k)) for y in range(1<<n)))
    print(dict(stats))

if __name__=='__main__':
    main()
