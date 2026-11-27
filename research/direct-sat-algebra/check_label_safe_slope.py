from random import Random
from label_safe_slope import expectation,find_columns
from additive_safe_slope import _columns
from additive_slope_prefix import dickson
from product_network_inequality import trace_dual
from product_slack import linearized
from punctured_witness import BinaryField
from quadratic_image import field_modulus

def direct(f, cols):
    A = [0]*f.size
    for x in range(1,f.size):
        i = (x & -x).bit_length()-1
        A[x] = A[x^(1<<i)] ^ cols[i]
    return set(range(f.size)) - {f.mul(A[x],f.inverse(x)) for x in range(1,f.size)}

def test():
    rng = Random(3762)
    witnesses = checks = singletons = 0
    for d in [2,3,4,5,7]:
        f = BinaryField(field_modulus(d))
        if d<=3:
            maps = [tuple((v>>(d*i)) % f.size for i in range(d)) for v in range(1<<(d*d))]
        else:
            maps = [tuple(rng.randrange(f.size) for _ in range(d)) for _ in range(8)]
        maps.extend(tuple(_columns(f,[s,1])) for s in range(min(f.size,8)))
        dual = trace_dual(f)
        for case, cols in enumerate(maps):
            good = direct(f,cols)
            singletons += len(good)==1
            assert find_columns(f,cols) in good
            witnesses += 1
            D = dickson(f,linearized(f,cols))
            if d==2 or case<8 or case%53==0:
                for k in range(min(d,3)+1):
                    for v in range(1<<k):
                        factors = [(1^(v>>i&1),dual[i]) for i in range(k)]
                        assert expectation(f,D,factors)==sum(s % (1<<k)==v for s in good)%2
                        checks += 1
    print(witnesses,'original answers;',singletons,'singleton maps;',checks,'affine prefixes')
if __name__ == '__main__':
    test()
