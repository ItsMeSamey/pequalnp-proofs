"""Direct code table and rank check for the triangle replacement counterexample."""
from itertools import combinations

edges = list(combinations(range(5),2))
cols = [(1 << (u-1) if u else 0) ^ (1 << (v-1)) for u,v in edges]
ports = [edges.index(e) for e in [(0,1),(0,2),(3,4)]]
portword = sum(1<<i for i in ports)

def apply(x):
    h=0
    for i,col in enumerate(cols):
        if x >> i & 1:
            h ^= col
    return h

ker={x for x in range(1<<len(cols)) if apply(x)==0}
joined = {x ^ t for x in ker for t in [0,portword]}
assert joined == {x for x in range(1<<len(cols)) if apply(x) in {0,15}}
assert {min(z,z^15) for z in cols} == set(range(1,8))
assert len(ker)==64 and len(joined)==128
print("Verified all 1024 K5 vectors and all 7 Fano quotient points")
