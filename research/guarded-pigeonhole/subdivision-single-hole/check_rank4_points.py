"""Complete labeled census on the 15 points of binary projective rank four."""
from itertools import product

def support(points):
    return sum(1<<x for x in points)

def points(mask):
    return [i for i in range(1,16) if mask>>i&1]

def forbidden_closure(P, kernels):
    possible_zero=0
    for ker in kernels:
        if not ker & P: possible_zero |= ker
    return 65534 & ~(possible_zero|P)

def run():
    kernels={support(v for v in range(1,16) if (a&v).bit_count()%2==0 and (b&v).bit_count()%2==0)
             for a,b in product(range(16),repeat=2)}
    planes=[K for K in kernels if K.bit_count()==7]
    plane_test=[any((s&H).bit_count()>=6 for H in planes) for s in range(65536)]
    stats=[0]*4; example=None
    for p in range(0,65536,2):
        xs=points(p)
        if plane_test[p]: continue
        # To obtain a rank-3 minor from rank <=4, at most one independent contraction is necessary.
        # If a rank-3 deletion minor exists, the plane test already detects it.
        if any(plane_test[support({min(b,b^a) for b in xs if b!=a})] for a in xs): continue
        stats[0]+=1
        extra=forbidden_closure(p,kernels)
        if extra:
            stats[1]+=1
            if example is None: example=xs,points(extra)
        if any(sum(b<(a^b) and ((p>>(a^b))&1) for b in xs)>2 for a in xs): continue
        stats[2]+=1
        if extra: stats[3]+=1
    assert stats==[12784,420,12364,0]
    print(stats,example)
if __name__=='__main__':run()
