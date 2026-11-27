"""Tiny independent rational ranks for parity-constrained phase matrices."""
from fractions import Fraction
from random import Random


def image(cols):
    vals=[0]
    for c in cols:vals.extend([v^c for v in vals])
    return vals


def real_rank(rows):
    pivots={}
    for row in rows:
        v=list(map(Fraction,row))
        for i in sorted(pivots):
            if v[i]:
                m=v[i]
                v=[a-m*b for a,b in zip(v,pivots[i])]
        i=next((i for i,vv in enumerate(v) if vv),None)
        if i is not None:pivots[i]=[a/v[i] for a in v]
    return len(pivots)


def check(A,B,J,t,left_sign=0,right_sign=0):
    # A,B list binary syndrome columns, J list right-coordinate row masks.
    av,bv,jv=map(image,(A,B,J))
    assert len(A)==len(J) and all(0<=j<1<<len(B) for j in J)
    rows=[[(0 if a^b!=t else (-1)**(((jv[u]&v).bit_count()+(left_sign>>u&1)+(right_sign>>v&1))%2))
           for v,b in enumerate(bv)] for u,a in enumerate(av)]
    actual=real_rank(rows)
    Ia,Ib=set(av),set(bv)
    if not any(t^a in Ib for a in Ia):
        assert actual==0
        return actual,None,None
    c=(len(Ia&Ib)).bit_length()-1
    ra,rb=(len(Ia).bit_length()-1,len(Ib).bit_length()-1)
    assert c==ra+rb-(len({a^b for a in Ia for b in Ib}).bit_length()-1)
    # Distinct restricted functionals on V_0 form an image of size 2^r.
    kernel_b=[v for v,b in enumerate(bv) if b==0]
    signatures={tuple((jv[u]&v).bit_count()%2 for v in kernel_b)
                for u,a in enumerate(av) if a==0}
    r=len(signatures).bit_length()-1
    assert actual==(1<<(c+r))
    return actual,c,r


if __name__=='__main__':
    assert check([],[],[],0)==(1,0,0)
    assert check([],[],[],1)==(0,None,None)
    assert check([],[1,0],[],1)==(1,0,0)
    assert check([1,2],[],[0,0],3)==(1,0,0)
    assert check([0,0],[0,0],[1,2],0)==(4,0,2)
    assert check([1,0],[1,0],[1,0],0)==(2,1,0)
    assert check([1,2],[4,8],[3,1],13)==(1,0,0)
    rng=Random(4802)
    for _ in range(250):
        a,b,k=(rng.randrange(4) for _ in range(3))
        A=[rng.randrange(1<<k) for i in range(a)]
        B=[rng.randrange(1<<k) for i in range(b)]
        J=[rng.randrange(1<<b) for i in range(a)]
        for t in range(1<<k):
            check(A,B,J,t,rng.getrandbits(1<<a),rng.getrandbits(1<<b))
    print('7 structured cases and all targets of 250 seeded instances passed')
