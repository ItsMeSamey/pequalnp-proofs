"""Independent source enumeration, including affine base changes and mixed identities."""
from itertools import product
from random import Random
from controlled_image_peeling import exact
from check_controlled_code_blocks import apply,legal

def check(m,A,b,U,q):
    n,k=len(A),len(U)
    source=sum(legal(A,b,U,q,x,y) for y in range(1<<n) for x in range(1<<k))
    for terminal in ("brute","character","auto"):
        count,witness,stats=exact(m,A,b,U,q,terminal=terminal)
        assert count==source,(m,A,b,U,q,count,source)
        assert (witness is None)==(source==0)
        if witness is not None:
            assert legal(A,b,U,q,*witness)
    return count,stats

def main():
    cases=0
    for a,b,u,v,f,c,g,d in product((0,1),repeat=8):
        check(1,[a],b,[u,v],[(f,c),(g,d)])
        cases+=1
    # Three distinct directions on the same linear activator add to a constant;
    # the repeated first map also provides a genuine null control.
    instance=(2,[2],1,[1,2,3,1],[(1,0),(1,0),(1,1),(1,0)])
    val,stats=check(*instance)
    assert stats["rounds"][0][3:]==(1,1,2)
    print("mixed affine maps",val,stats)
    val,stats=check(3,[4,1],0,[1,2],[(1,0),(2,0)])
    assert [r[2] for r in stats["rounds"]]==[1,0,0]
    print("successive data restrictions",val,stats)
    rng=Random(820206)
    recodes=0
    for _ in range(350):
        m,n,k=[rng.randrange(6) for _ in range(3)]
        A=[rng.randrange(1<<m) for _ in range(n)]
        b=rng.randrange(1<<m)
        U=[rng.randrange(1<<m) for _ in range(k)]
        q=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(k)]
        ref,_=check(m,A,b,U,q)
        cases+=1
        if m<2 or n<2: continue
        def basis(d):
            columns=[1<<i for i in range(d)]
            for _ in range(3*d*d):
                i,j=rng.sample(range(d),2)
                columns[i]^=columns[j]
            return columns
        B,C=basis(n),basis(m)
        shift=rng.randrange(1<<n)
        order=rng.sample(range(k),k)
        A2=[apply(C,apply(A,col)) for col in B]
        q2=[(sum(((v&t).bit_count()%2)<<j for j,t in enumerate(B)),c^((v&shift).bit_count()%2))
            for v,c in q]
        args=(m,A2,apply(C,b^apply(A,shift)),[apply(C,U[j]) for j in order],[q2[j] for j in order])
        got,_=check(*args)
        assert got==ref
        _,wit,_=exact(*args)
        if wit is not None:
            x,y=wit
            oldx=sum(((x>>i)&1)<<j for i,j in enumerate(order))
            assert legal(A,b,U,q,oldx,apply(B,y)^shift)
        recodes+=1
    print("originals",cases+2,"recodings",recodes)
if __name__=="__main__": main()
