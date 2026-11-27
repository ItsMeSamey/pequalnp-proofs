"""Compare pinned Pfaffian parity with raw binary ranks on entire selected lines."""
from random import Random
from additive_safe_slope import _safe
from labeled_paired_line import Line,find_columns
from product_network_inequality import trace_dual
from punctured_witness import BinaryField
from quadratic_target import apply_basis

rng=Random(992321)
parities=0
witnesses=0
for modulus,trials,depth in ((7,2,0),(19,3,1),(67,3,2),(283,2,2),(1033,1,3)):
    f=BinaryField(modulus)
    d=f.m
    dual=trace_dual(f)
    for trial in range(trials):
        center=rng.randrange(f.size)
        form=[0]*d
        for _ in range((d-2)//2):
            x,y=rng.getrandbits(d),rng.getrandbits(d)
            for j in range(d):
                form[j]^=(x if y>>j&1 else 0)^(y if x>>j&1 else 0)
        cols=[apply_basis(dual,v)^f.mul(center,1<<j) for j,v in enumerate(form)]
        line=Line(f,cols)
        assert line.scale is not None and line.center==center
        good=[_safe(f,cols,center^f.mul(line.scale,apply_basis(line.basis,z)))
              for z in range(1<<line.a)]
        for h in range(depth+1):
            for prefix in range(1<<h):
                assert line.parity(prefix,h)==line.parity(prefix,h,stream=True)==sum(good[prefix::1<<h])%2
                parities+=1
        assert _safe(f,cols,find_columns(f,cols,depth))
        assert _safe(f,cols,find_columns(f,cols,depth,stream=True))
        witnesses+=1
print(parities,"complete prefix parities and",witnesses,"raw witness replays passed")

f=BinaryField(0x1100b)
d=f.m
center=1371
x,y=0x84ee,0x7626
dual=trace_dual(f)
columns=[apply_basis(dual,(x if y>>j&1 else 0)^(y if x>>j&1 else 0))^f.mul(center,1<<j) for j in range(d)]
assert _safe(f,columns,find_columns(f,columns))
assert _safe(f,columns,find_columns(f,columns,stream=True))
print("degree-16 default-depth raw witness passed, both storage modes")
