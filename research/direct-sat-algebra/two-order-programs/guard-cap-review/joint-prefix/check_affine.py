from affine_lift import join_affine,extend_affine
from itertools import product
def xor(ids,b):
    return [tuple(-v if a else v for a,v in zip(vals,ids)) for vals in product((0,1),repeat=len(ids)) if sum(vals)%2!=b]
# Boundary x2,x3,x4 has ternary parity differing by s, via private x5.
pre=xor((1,2,5),0)+xor((3,4,5),0); B=(2,3,4)
a=join_affine(6,pre,xor((2,6),0),B,[-1],[1])
assert a.status=="LIFT" and (a.shift&14).bit_count()%2==1
for vals in product((0,1),repeat=3):
    if sum(vals)%2: continue
    moved=[v if b^(bool(a.shift&(1<<(v-1)))) else -v for v,b in zip(B,vals)]
    assert extend_affine(6,pre,[1],moved) is not None
assert join_affine(6,pre,[],B,[-1],[1],fixed=B).status=="NO_GROUP_LIFT"
assert join_affine(6,[(1,),(1,-2)],[],[],[-1],[1]).status=="NO_GROUP_LIFT"
assert join_affine(6,[()],[],[],[-1],[1]).status=="LIFT"
print("projected ternary parity, raw lifts, immutable boundary and empty affine supports passed")
