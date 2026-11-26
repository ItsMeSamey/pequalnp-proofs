"""Check guarded sign clauses and Kasteleyn evaluation on a 4x4 grid."""
from itertools import product
from functools import cache
from sympy import Matrix

L = 4
VERTICES = tuple(product(range(L),repeat=2))
EDGES = tuple((a,b) for a in VERTICES for b in VERTICES if a<b
              and sum(abs(i-j) for i,j in zip(a,b))==1)
BLACK = tuple(v for v in VERTICES if sum(v)%2==0)
WHITE = tuple(v for v in VERTICES if sum(v)%2)
MARKED = tuple(EDGES.index(((r,c),(r,c+1))) for r,c in product((0,2),repeat=2))


def matchings(remaining):
    if not remaining:
        yield frozenset()
        return
    v = min(remaining)
    for i,e in enumerate(EDGES):
        if v in e and remaining.issuperset(e):
            for tail in matchings(remaining.difference(e)):
                yield tail | {i}


def sign_factor(bits, a, s):
    # Units force all guards zero in every contributing assignment.
    if bits!=a:
        return [0]*5
    pol = [1,0,0,0,0]
    for i in range(4):
        # A positive second literal gives -z*x; a negative gives 1+z*x.
        positive = (s>>i)&1
        c = 1-positive
        slope = (1-2*positive)*((bits>>i)&1)
        pol = [c*pol[j]+(slope*pol[j-1] if j else 0) for j in range(5)]
    return pol


def determinant(a,s,z):
    # Vertex exactly-one CNF and pinned literals leave forced marked edge states.
    # Restricted edges get a zero weight or else are forced by deleting endpoints.
    forced = {MARKED[i] for i in range(4) if (a>>i)&1}
    removed = {v for i in forced for v in EDGES[i]}
    # Keep all endpoints: at a forced dimer zero its competing incident edges.
    mat = [[0]*len(WHITE) for _ in BLACK]
    outside = 1
    for i,d in enumerate(MARKED):
        bit = (a>>i)&1
        outside *= (-z*bit if (s>>i)&1 else 1+z*bit)
    for i,(v,w) in enumerate(EDGES):
        if i not in forced and (i in MARKED or v in removed or w in removed):
            continue
        b,wh = (v,w) if v in BLACK else (w,v)
        mat[BLACK.index(b)][WHITE.index(wh)] = (-1)**v[1] if v[1]==w[1] else 1
    return outside*Matrix(mat).det()


if __name__=='__main__':
    histogram = [0]*16
    for m in matchings(set(VERTICES)):
        bits = sum(1<<i for i,edge in enumerate(MARKED) if edge in m)
        histogram[bits] += 1
    assert sum(histogram)==36 and min(histogram)>0
    # Fix one global orientation sign from a positive partition function.
    orientation = 1 if determinant(0,0,0)>0 else -1
    determinants = [orientation*determinant(a,0,0) for a in range(16)]
    assert determinants==histogram
    for a,s in product(range(16),repeat=2):
        coeff = [histogram[a]*v for v in sign_factor(a,a,s)]
        for z in (-2,-1,0,1,2):
            # Reuse the already verified restricted determinant for all parameters.
            scaled = determinants[a]
            for i in range(4):
                bit = (a>>i)&1
                scaled *= -z*bit if (s>>i)&1 else 1+z*bit
            assert sum(c*z**j for j,c in enumerate(coeff))==scaled
        if a.bit_count()==s.bit_count():
            j = s.bit_count()
            assert coeff[j]==(-1)**j*histogram[a]*int(a==s)
    for j in range(5):
        indices = [i for i in range(16) if i.bit_count()==j]
        mat = Matrix([[histogram[a]*sign_factor(a,a,s)[j] for s in indices] for a in indices])
        assert mat.rank()==len(indices)
    print('matching counts',histogram,'; ranks by degree', [1,4,6,4,1])
