from itertools import product
from random import Random
from additive_safe_slope import _columns,_safe,moment
from additive_slope_prefix import find,dickson,dickson_moment
from check_additive_safe_slope import F2
from punctured_witness import BinaryField


def check():
    rng=Random(672)
    checked=0
    for f in (F2(),BinaryField(7),BinaryField(11),BinaryField(19),BinaryField(37)):
        q=f.size
        cases=(product(range(q),repeat=f.m) if q<=8 else
               [tuple(rng.randrange(q) for _ in range(f.m)) for _ in range(20)])
        for a in cases:
            D=dickson(f,a)
            for t in range(2*q+1):
                assert dickson_moment(f,D,t)==moment(f,a,t)
            cols=_columns(f,a)
            safe=[s for s in range(q) if _safe(f,cols,s)]
            prefix=0
            for h in range(f.m+1):
                if h:
                    zero_count=sum((s & ((1<<h)-1))==prefix for s in safe)
                    if not zero_count%2: prefix |= 1<<(h-1)
                s=find(f,a,prefix_bits=h)
                assert s in safe and (s & ((1<<h)-1))==prefix
                checked+=1
            assert find(f,a) in safe
    f=BinaryField(283)
    for a in (0,1,59,204):
        assert find(f,[a,1])==a
    print(checked,"explicit prefix parities and witnesses matched; default GF256 unique-safe cases passed")


if __name__=="__main__":
    check()
