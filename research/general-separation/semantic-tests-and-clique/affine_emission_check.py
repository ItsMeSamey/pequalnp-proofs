"""Compare actual first hits with the Boolean degree bound under affine iteration."""
from itertools import product
from math import comb, prod
from random import Random

def affine_map(rows,x,s):
    return sum(((((a & x).bit_count() + (a>>s)) & 1) << i) for i,a in enumerate(rows))

def hits(nexts,flags,s,e):
    limit=sum(comb(s,j) for j in range(e+1))-1
    for x in range(1<<s):
        seen=0
        order=[]
        while not (seen>>x&1):
            seen |= 1<<x
            order.append(x)
            x=nexts[x]
        for flag in flags:
            if flag&seen:
                assert next(i for i,x in enumerate(order) if flag>>x&1)<=limit

rng=Random(197)
count=0
for s in range(1,4):
    n=1<<s
    mon=[sum(int(x&m==m)<<x for x in range(n)) for m in range(n)]
    linear=[sum((((a&x).bit_count()+(a>>s))%2)<<x for x in range(n)) for a in range(2*n)]
    quad=[]
    for _ in range(6):
        val=0
        for m,tab in enumerate(mon):
            if m.bit_count()<=2 and rng.getrandbits(1):
                val ^= tab
        quad.append(val)
    for rows in product(range(2*n),repeat=s):
        fn=[affine_map(rows,x,s) for x in range(n)]
        hits(fn,linear,s,1)
        hits(fn,quad,s,min(2,s))
        count+=1
for lengths in [(2,),(2,3),(2,3,5),(2,3,5,7)]:
    blocks=[1]*len(lengths)
    for tick in range(prod(lengths)):
        flag=all(b==(1<<(l-1)) for b,l in zip(blocks,lengths))
        assert flag==(tick==prod(lengths)-1)
        blocks=[((b<<1)&((1<<l)-1))|(b>>(l-1)) for b,l in zip(blocks,lengths)]
for s in range(1,13):
    b,t,h=0,1,0
    mask=(1<<s)-1
    ticks=0
    while not h:
        assert t.bit_count()==1
        h=(t&b)>>(s-1)
        return_bit=((t&(b^mask)).bit_count()+h)&1
        b,t=(b^t),(((t&b)<<1)&mask)|return_bit
        ticks+=1
        assert ticks<=2**(s+1)-2
    assert ticks==2**(s+1)-2 and (b,t)==(0,1)
print(count,'affine maps; four coprime examples; exact odometer hits for 1..12 bits')
