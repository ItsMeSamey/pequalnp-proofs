"""Decode arbitrary nonsingular two-bit edge pairings in recovered plane bases."""
from graph_derivation import recover as recover_graph
from quadratic_centroid import independent
from quadratic_target import apply_basis, interpolate


def recover(n,m,constant,linear,pairs):
    """Return GainGraph or None. Matrix entry (i,j) occupies bit 2*i+j."""
    return recover_graph(n,m,constant,linear,pairs,gains=True)


def pairing(matrix,x,y):
    return sum(((x>>i)&(y>>j)&(matrix>>(2*i+j))&1)
               for i in range(2) for j in range(2))%2


def self_test():
    from random import Random
    rng=Random(217)
    def random_basis(d):
        b=()
        while len(b)<d:
            b=independent((*b,rng.randrange(1,1<<d)))
        return b
    for twist in (6,9,7):
        # Four determinant edges fix one common frame. The last edge can be
        # synchronized exactly when its matrix is also the determinant J=6.
        ib,ob=random_basis(10),random_basis(5)
        shift,offset=rng.randrange(1024),rng.randrange(32)
        def original(x):
            z=apply_basis(ib,x^shift)
            codes=[(z>>(2*j))&3 for j in range(5)]
            y=sum(pairing(6 if j<4 else twist,codes[j],codes[(j+1)%5])<<j
                  for j in range(5))
            return apply_basis(ob,y)^offset
        c,l,q=interpolate(original,10)
        graph=recover(10,5,c,l,q)
        assert graph is not None
        assert (recover_graph(10,5,c,l,q) is not None)==(twist==6)
        frame=tuple(v for p in graph.planes for v in p)
        for z in range(1024):
            y=graph.output_offset
            for u,v,e,h in graph.edges:
                if pairing(h,(z>>(2*u))&3,(z>>(2*v))&3):
                    y^=e
            assert y==original(graph.shift^apply_basis(frame,z))
    print("three hidden cycles, including two inconsistent gains, checked at all inputs")


if __name__=="__main__":
    self_test()
