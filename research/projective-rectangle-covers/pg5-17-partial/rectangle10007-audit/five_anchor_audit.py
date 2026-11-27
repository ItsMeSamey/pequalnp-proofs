"""Independent finite-integer audit of the area-52 necessity."""
from fractions import Fraction as F
from functools import lru_cache
from math import ceil
D=lambda e:F(120*e*e,625+50*e+121*e*e)
s,b=F(17125,93899),F(3030,93899)
assert all(D(e)<=s*e+b for e in range(401))
assert all(D(e)<=s*e for e in range(0,401,5))
assert ceil((14-31*b)/s)==72
@lru_cache(None)
def loss(vertices, exceptional, excess):
    if not vertices:
        return F(0) if not excess else None
    step=1 if exceptional else 5
    options=[]
    for e in range(0,excess+1,step):
        past=loss(vertices-1,max(0,exceptional-1),excess-e)
        if past is not None:
            options.append(D(e)+past)
    return max(options,default=None)

for n49 in range(4):
    for n48 in range(2):
        if n49+2*n48>3:
            continue
        # With possible transposes the cheaper shore touches no more than this.
        special=(14*n49+19*n48)//2
        E=75-n49-2*n48
        crude=s*E+b*special
        exact=loss(31,special,E)
        assert exact is not None and exact<=crude<14
        print(n49,n48,special,E,round(float(exact),6))
