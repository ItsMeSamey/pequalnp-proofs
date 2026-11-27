"""Small exact dispatcher and raw-bit witness controls for scheduler 04."""
from itertools import product
from shell_dispatch import choose_backend, dispatch_block_witness


def main():
    for d,r in product(range(9),repeat=2):
        expected='affine' if 3**d<=2**(r+d) else 'fourier'
        assert choose_backend(d,r)==expected
    for pins in ([],[(0,2,0)],[(0,2,0),(1,3,0)],[(0,2,0),(2,0,1)]):
        words={w for w in product((0,1),repeat=4)
               if w[:2]!=w[2:] and all((w[a]^w[b])==s for a,b,s in pins)}
        for method in ('affine','fourier','auto'):
            w=dispatch_block_witness(1,pins,method=method)
            assert (w is not None)==bool(words)
            if w is not None:assert tuple(w) in words
    print('81 dimension/codimension comparisons and 12 original branch verdicts')


if __name__=='__main__':main()
