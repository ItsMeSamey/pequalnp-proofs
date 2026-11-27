"""Three nonzero GF4 pins on a supplied Hermitian self-dual code.

Words are packed site pairs with 1,2,3 denoting 1,omega,omega+1. Input generators
are binary generators of the promised GF4-linear code. The first three sites
are the pins (permute sites first for other triples).
"""
from collections import deque
from itertools import combinations,product
from random import Random
from hexacode_pin_strips_check import hexacode,binary_basis


def mul(a,b):
    return ((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))[a][b]


def ratio(a,b):
    return next(t for t in (1,2,3) if mul(t,b)==a)


def coord(w,i):
    return w>>(2*i)&3


def scale(w,t,n):
    return sum(mul(coord(w,i),t)<<(2*i) for i in range(n))


def even_witness(A,color,d):
    if not d:return 0
    if d in color:return 1<<color.index(d)
    a,b=[i for i in (1,2,3) if i!=d]
    E=[i for i,c in enumerate(color) if c==a]
    F=[i for i,c in enumerate(color) if c==b]
    for i,j in product(E,F):
        if not A[i]>>j&1:return (1<<i)|(1<<j)
    prev=dict.fromkeys(E)
    queue=deque(E)
    while queue:
        u=queue.popleft()
        for v,c in enumerate(color):
            if not A[u]>>v&1 or v in prev or c==a or (color[u]==a and c==b):continue
            prev[v]=u
            if c==b:
                out=0
                while v is not None:out|=1<<v;v=prev[v]
                return out
            queue.append(v)
    return None


def solve(n,generators,pins):
    a,b,c=pins
    u=ratio(b,a)
    v=ratio(a,c)
    # Enforce site 1 = u * site 0, keeping basis vectors in original coordinates.
    constraint={}
    accepted=[]
    for word in generators:
        s=coord(word,1)^mul(u,coord(word,0))
        while s and s.bit_length() in constraint:
            t,lift=constraint[s.bit_length()]
            s^=t;word^=lift
        if s:constraint[s.bit_length()]=s,word
        else:accepted.append(word)
    # Image under puncturing, with one preimage per basis row and pure kernel.
    basis={};pure=[]
    for word in accepted:
        while word>>4 and word.bit_length() in basis:word^=basis[word.bit_length()]
        if word>>4:basis[word.bit_length()]=word
        elif word:pure.append(word)
    nres=n-2
    rows=[[w>>4,w] for w in basis.values()]
    assert len(rows)==nres
    def pivot():
        k=0;chosen=[]
        for j in range(nres):
            bit=2*j
            hit=next((i for i in range(k,nres) if rows[i][0]>>bit&1),None)
            if hit is None:continue
            rows[k],rows[hit]=rows[hit],rows[k]
            for i in range(nres):
                if i!=k and rows[i][0]>>bit&1:
                    rows[i][0]^=rows[k][0];rows[i][1]^=rows[k][1]
            chosen.append(j);k+=1
        return chosen
    swaps=0
    while True:
        chosen=pivot()
        if len(chosen)==nres:break
        kernel=rows[len(chosen)][0]
        j=next(j for j in range(nres) if j not in chosen and kernel>>(2*j+1)&1)
        for row in rows:
            if coord(row[0],j) in (1,2):row[0]^=3<<(2*j)
        swaps+=1
    shears=0
    for i in range(nres):
        if coord(rows[i][0],i)==3:
            shears+=1
            for row in rows:
                if row[0]>>(2*i)&1:row[0]^=2<<(2*i)
    A=[sum(((w>>(2*j+1))&1)<<j for j in range(nres)) for w,_ in rows]
    assert all(row.bit_count()%2==1 and not row>>i&1 for i,row in enumerate(A))
    assert all((A[i]>>j&1)==(A[j]>>i&1) for i,j in combinations(range(nres),2))
    # For nonpure lifts the equality first = v*third is homogeneous in graph x.
    # Under x=1+z, its target on z is the sum of all column colors.
    colors=[coord(lift,0)^mul(v,coord(lift,2)) for _,lift in rows]
    target=0
    for sym in colors:target^=sym
    z=0 if pure else even_witness(A,colors,target)
    if z is None:return None,(bool(pure),swaps,shears)
    lift=0
    for i,(_,w) in enumerate(rows):
        if not z>>i&1:lift^=w
    if pure:
        delta=coord(lift,0)^mul(v,coord(lift,2))
        if delta:lift^=scale(pure[0],ratio(delta,coord(pure[0],0)),n)
    assert all(coord(lift,i) for i in range(n))
    lift=scale(lift,ratio(c,coord(lift,2)),n)
    assert tuple(coord(lift,i) for i in range(3))==pins
    return lift,(bool(pure),swaps,shears)


def check(rows,rng,trials):
    n=len(rows[0])
    stats=[0]*4
    for _ in range(trials):
        order=rng.sample(range(n),n)
        factors=[rng.randrange(1,4) for _ in order]
        words={sum(mul(w[j],factors[i])<<(2*i) for i,j in enumerate(order)) for w in rows}
        gen=binary_basis(words)
        valid={tuple(coord(w,i) for i in range(3)) for w in words if all(coord(w,i) for i in range(n))}
        for pins in product((1,2,3),repeat=3):
            result,(pure,swaps,shears)=solve(n,gen,pins)
            assert (result is not None)==(pins in valid)
            if result is not None:assert result in words
            for i,val in enumerate((pure,swaps>0,shears>0,result is None)):stats[i]+=val
    return stats


if __name__=='__main__':
    rng=Random(1486)
    words=hexacode()
    pure=[(a,a,b,b,c,c) for a,b,c in product(range(4),repeat=3)]
    glued=[a[:5]+b[1:] for a,b in product(words,repeat=2) if a[5]==b[0]]
    for label,C,k in [('wheel',words,12),('pure pairs',pure,18),('glued',glued,6)]:
        print(label,k*27,check(C,rng,k))

    random_rows=pure
    for _ in range(8):
        # Hermitian transvection about an even-weight (isotropic) field vector.
        h=[0]*6
        for j in rng.sample(range(6),4):h[j]=rng.randrange(1,4)
        changed=[]
        for w in random_rows:
            coeff=0
            for x,y in zip(w,h):coeff^=mul(x,mul(y,y))
            changed.append(tuple(x^mul(coeff,y) for x,y in zip(w,h)))
        random_rows=changed
        check(random_rows,rng,1)
    print('216 additional random Hermitian transvection controls passed')
