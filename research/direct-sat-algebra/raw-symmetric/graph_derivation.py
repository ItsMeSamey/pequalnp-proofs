"""Recognize packed vector quadratic maps as affinely recoded graph determinants.

For a successful result use recovered plane coordinates z. Then Q(shift+z)
equals output_offset plus the determinants weighted by the recovered edge
vectors. None means that this recognition procedure is inconclusive.
"""
from dataclasses import dataclass
from itertools import combinations
from quadratic_centroid import independent, zero_combinations
from quadratic_target import (affine_domain, apply_basis, evaluate_anf, insert,
                              interpolate, reduce_vector)


@dataclass(frozen=True)
class Graph:
    planes: tuple
    edges: tuple   # triples (u,v,ambient output basis vector)
    shift: int
    output_offset: int


@dataclass(frozen=True)
class GainGraph:
    planes: tuple
    edges: tuple  # (u,v,output vector,2x2 matrix packed by rows)
    shift: int
    output_offset: int


def recover(n,m,constant,linear,pairs, *, gains=False):
    """With gains=True, certify arbitrary invertible binary edge pairings."""
    if min(n,m,constant)<0 or len(linear)!=n or any(
            v<0 or v.bit_length()>m for v in (constant,*linear,*pairs.values())) or any(
            not 0<=i<j<n for i,j in pairs):
        raise ValueError("invalid packed ANF")
    if n%2 or not m:
        return None
    unit = tuple(1<<i for i in range(n))
    ij = tuple(combinations(range(n),2))
    image = [pairs.get(e,0) for e in ij]
    base = independent(image)
    if len(base)!=m:
        return None
    rows = {}
    for j,v in enumerate(base):
        insert(v,1<<j,rows)
    coords = [reduce_vector(v,rows)[1] for v in image]
    basis_indices = [image.index(v) for v in base]
    polar = [tuple(pairs.get(tuple(sorted((i,j))),0) for i in range(n)) for j in range(n)]
    def b(x,y):
        z = 0
        while y:
            bit = y & -y
            z ^= apply_basis(polar[bit.bit_length()-1],x)
            y ^= bit
        return z
    def matrix(v):
        return tuple((v>>(n*i)) & ((1<<n)-1) for i in range(n))
    def pack(cols,width):
        return sum(v<<(width*i) for i,v in enumerate(cols))
    def derivation_defect(v):
        # Full polar image uniquely determines T from S on an output basis.
        s = matrix(v)
        rhs = [apply_basis(polar[j],s[i]) ^ apply_basis(polar[i],s[j]) for i,j in ij]
        t = [rhs[i] for i in basis_indices]
        return pack([h ^ apply_basis(t,c) for h,c in zip(rhs,coords)],m)
    derivations = zero_combinations((1<<i for i in range(n*n)),derivation_defect)
    matrices = [matrix(v) for v in derivations]
    def commutators(v):
        s = matrix(v)
        return pack([apply_basis(s,t[i]) ^ apply_basis(t,s[i])
                     for t in matrices for i in range(n)],n)
    center = zero_combinations(derivations,commutators)
    # The center can include nonsplit operators. On a commuting binary
    # space E -> E^2+E is linear even if its image leaves that space.
    def projector_defect(v):
        s = matrix(v)
        return pack([apply_basis(s,x)^x for x in s],n)
    projectors = zero_combinations(center,projector_defect)
    planes = [unit]
    for v in projectors:
        s = matrix(v)
        finer = []
        for plane in planes:
            zero = zero_combinations(plane,lambda x:apply_basis(s,x))
            one = zero_combinations(plane,lambda x:apply_basis(s,x)^x)
            if len(zero)+len(one)!=len(plane):
                return None
            finer.extend(u for u in (zero,one) if u)
        planes = finer
    if any(len(u)!=2 or b(*u) for u in planes):
        return None
    edges = []
    adj = [[] for _ in planes]
    for i,j in combinations(range(len(planes)),2):
        values = [b(x,y) for x in planes[i] for y in planes[j]]
        line = independent(values)
        if not line:
            continue
        if len(line)!=1 or not ((bool(values[0]) and bool(values[3])) ^
                                (bool(values[1]) and bool(values[2]))):
            return None
        e, = line
        edges.append((i,j,e))
        adj[i].append((j,e))
        adj[j].append((i,e))
    if len(edges)!=m or len(independent(e for i,j,e in edges))!=m:
        return None
    oriented = [None]*len(planes)
    if gains:
        oriented = [tuple(p) for p in planes]
    for root in range(len(planes)):
        if oriented[root] is not None:
            continue
        oriented[root] = tuple(planes[root])
        stack = [root]
        while stack:
            i = stack.pop()
            for j,e in adj[i]:
                def matches(frame):
                    return tuple(b(x,y) for x in oriented[i] for y in frame)==(0,e,e,0)
                if oriented[j] is not None:
                    if not matches(oriented[j]):
                        return None
                else:
                    u,v = planes[j]
                    vectors = (u,v,u^v)
                    oriented[j] = next(((x,y) for x in vectors for y in vectors
                                        if x!=y and matches((x,y))),None)
                    if oriented[j] is None:
                        return None
                    stack.append(j)
    # The discrepancy has zero polar. Solve for a translation explaining its
    # values on the recovered domain basis.
    equations = []
    for plane in oriented:
        for x in plane:
            d = evaluate_anf(0,linear,pairs,x)
            columns = [b(x,y) for y in unit]
            for j in range(m):
                equations.append((sum(((v>>j)&1)<<i for i,v in enumerate(columns)),(d>>j)&1))
    chart = affine_domain(n,equations)
    if chart is None:
        return None
    shift = chart[0]
    output_offset = evaluate_anf(constant,linear,pairs,shift)
    if gains:
        pairings = []
        for i,j,e in edges:
            entries = [b(x,y) for x in oriented[i] for y in oriented[j]]
            pairing = sum(int(v==e)<<k for k,v in enumerate(entries))
            pairings.append((i,j,e,pairing))
        return GainGraph(tuple(oriented),tuple(pairings),shift,output_offset)
    return Graph(tuple(oriented),tuple(edges),shift,output_offset)


def self_test():
    from random import Random
    rng = Random(219)
    def random_basis(n):
        basis = ()
        while len(basis)<n:
            basis = independent((*basis,rng.randrange(1,1<<n)))
        return basis
    def test_fixture(edges,vertices,accepted):
        n,m = 2*vertices,len(edges)
        ib,ob = random_basis(n),random_basis(m)
        t,c = rng.randrange(1<<n),rng.randrange(1<<m)
        def raw(x):
            z = apply_basis(ib,x^t)
            v = 0
            for k,(a,b) in enumerate(edges):
                i,j = 2*a,2*b
                v |= ((((z>>i)&(z>>(j+1))) ^ ((z>>(i+1))&(z>>j)))&1)<<k
            return apply_basis(ob,v)^c
        data = interpolate(raw,n)
        answer = recover(n,m,*data)
        assert (answer is not None)==accepted
        if answer is not None:
            frame = tuple(x for u in answer.planes for x in u)
            def reconstructed(z):
                out = answer.output_offset
                for a,b,e in answer.edges:
                    i,j = 2*a,2*b
                    if (((z>>i)&(z>>(j+1))) ^ ((z>>(i+1))&(z>>j)))&1:
                        out ^= e
                return out
            for z in (range(1<<n) if n<=10 else (rng.randrange(1<<n) for _ in range(300))):
                assert reconstructed(z)==raw(apply_basis(frame,z)^answer.shift)
    test_fixture([(i,(i+1)%5) for i in range(5)],5,True)
    test_fixture([(i,j) for i in range(3) for j in range(3,6)],6,False)
    petersen = [(i,(i+1)%5) for i in range(5)]+[(i,5+i) for i in range(5)]+[
        (5+i,5+(i+2)%5) for i in range(5)]
    test_fixture(petersen,10,True)
    print("recoded and translated C5, Petersen and K3,3 controls passed")


if __name__=="__main__":
    self_test()
