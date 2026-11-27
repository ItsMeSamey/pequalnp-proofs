from random import Random
from additive_safe_slope import _columns,_safe
from additive_slope_prefix import dickson
from label_safe_slope import expectation as dense
from label_safe_slope_stream import expectation,find_columns
from punctured_witness import BinaryField

rng=Random(7971)
checks=0
for modulus in (7,11,19,37):
    f=BinaryField(modulus)
    for trial in range(3):
        a=[rng.randrange(f.size) for _ in range(f.m)] if trial else [0,1]+[0]*(f.m-2)
        D=dickson(f,a)
        cols=_columns(f,a)
        good=[s for s in range(f.size) if _safe(f,cols,s)]
        for h in range(f.m+2):
            factors=[(rng.randrange(2),rng.randrange(f.size)) for _ in range(h)]
            if h>=2 and trial==1:factors[-1]=factors[0]
            expected=sum(all(c^f.trace(f.mul(alpha,s)) for c,alpha in factors) for s in good)%2
            assert expectation(f,D,factors)==expected==dense(f,D,factors)
            checks+=1
        for depth in (0,None,f.m):
            assert find_columns(f,cols,depth) in good
print(checks,"streamed/dense/direct parities and 36 original-coordinate searches passed")
