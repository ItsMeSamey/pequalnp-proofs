from random import Random
from additive_safe_slope import _columns, _safe
from punctured_witness import BinaryField
from quadratic_image import field_modulus
from selfadjoint_coset_sampler import subfield_basis
from quadratic_target import apply_basis
from sparse_line_prefix import find_columns

def check():
    rng = Random(235781)
    count = 0
    for d in (2,4,6,8,10,12,18):
        f = BinaryField(field_modulus(d))
        basis = subfield_basis(f)
        for trial in range(5):
            c = [rng.randrange(f.size)] + [0]*(d-1)
            c[d//2] = apply_basis(basis,rng.randrange(1 << len(basis)))
            for i in range(1,d//2):
                v = c[i] = rng.randrange(f.size)
                for _ in range(d-i):
                    v = f.mul(v,v)
                c[-i] = v
            cols = _columns(f,c)
            for h in (None,1,min(2,d//2)):
                assert _safe(f,cols,find_columns(f,cols,h))
                count += 1
    f = BinaryField(283)
    cols = [84,160,83,203,222,103,63,181]
    for h in range(5):
        assert _safe(f,cols,find_columns(f,cols,h))
        count += 1
    print(count,'original-column witness replays')

if __name__ == '__main__':
    check()
