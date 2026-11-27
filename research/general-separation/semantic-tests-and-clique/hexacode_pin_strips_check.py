"""Nowhere-zero signatures for the wheel chart and its GF(4) one-port gluings."""
from itertools import combinations,product
from random import Random


def hexacode():
    rows=[]
    for x in range(64):
        rim=[(x>>((i-1)%5)^x>>((i+1)%5)^x>>5)&1 for i in range(5)]
        hub=(x&31).bit_count()%2
        rows.append(tuple((x>>i&1)|(y<<1) for i,y in enumerate(rim))+(hub|((x>>5)<<1),))
    return rows


def sig(rows,indices):
    return {tuple(w[i] for i in indices) for w in rows if 0 not in w}


def pieces(t):
    # Within each hexagon the left/right connector sites are 0 and 5.
    return [[i for i in range(6) if (j==0 or i!=0) and (j==t-1 or i!=5)] for j in range(t)]


def strip_count(t,pins,words):
    # Pins are (block, site) -> specified nonzero symbol; internal symbols may be zero.
    state={None:1}
    for j,observed in enumerate(pieces(t)):
        new={}
        for w in words:
            if not all(w[i] and w[i]==pins.get((j,i),w[i]) for i in observed):continue
            left=w[0] if j else None
            right=w[5] if j+1<t else None
            new[right]=new.get(right,0)+state.get(left,0)
        state=new
    return state.get(None,0)


def binary_basis(values):
    pivots={}
    for x in values:
        while x:
            k=x.bit_length()
            if k not in pivots:
                pivots[k]=x;break
            x^=pivots[k]
    return list(pivots.values())


def check_code(rows):
    n=len(rows[0])
    packed=[sum(a<<(2*i) for i,a in enumerate(w)) for w in rows]
    gen=binary_basis(packed)
    assert len(gen)==n and len(set(packed))==1<<n
    assert all((b,)*n in rows for b in range(4))
    words=set(rows)
    assert all(tuple((0,2,3,1)[a] for a in w) in words for w in rows)
    # Sitewise endomorphisms preserve C iff all transformed generators pair
    # symplectically to zero with every generator of the self-dual code.
    constraints=[]
    for x,y in product(gen,repeat=2):
        row=0;pair=0
        for i in range(n):
            a,b=(x>>(2*i))&1,(x>>(2*i+1))&1
            c,d=(y>>(2*i))&1,(y>>(2*i+1))&1
            pair^=(a*d)^(b*c)
            row|=((a*d)|((b*d)<<1)|((a*c)<<2)|((b*c)<<3))<<(4*i)
        assert pair==0
        constraints.append(row)
    assert 4*n-len(binary_basis(constraints))==2


if __name__=='__main__':
    words=hexacode()
    check_code(words)
    assert sum(0 not in w for w in words)==18
    for tri in combinations(range(6),3):
        assert len({tuple(w[i] for i in tri) for w in words})==64
        assert len(sig(words,tri))==18
    tri=(0,1,2)
    missing=sorted(set(product((1,2,3),repeat=3))-sig(words,tri))
    print('rim triple',tri,'missing',missing)
    print('wheel pin-rim pairs with pinned hub and required (2,2,1)',
          [((a,b),(2,2,1) in sig(words,(a,b,5))) for a,b in combinations(range(5),2)])
    glued=[u[:5]+v[1:] for u,v in product(words,repeat=2) if u[5]==v[0]]
    check_code(glued)
    sites=[(j,i) for j,observed in enumerate(pieces(2)) for i in observed]
    rng=Random(997)
    for _ in range(128):
        pin={s:rng.randrange(1,4) for s in rng.sample(sites,3)}
        actual=sum(0 not in w and all(w[sites.index(s)]==b for s,b in pin.items()) for w in glued)
        assert strip_count(2,pin,words)==actual
    for k in (1,2,8):
        assert strip_count(k,{},words)>0
    print('length ten: dimension five, nonsplit; full-support words',strip_count(2,{},words))
    print('eight-block count',strip_count(8,{},words))
