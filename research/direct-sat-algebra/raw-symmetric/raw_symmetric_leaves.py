"""Certify a raw leaf space from commutator images of scalar polar ratios."""
from dataclasses import dataclass
from itertools import combinations
from binary_symmetric_pairing import recover as check_pairing
from binary_matrix_algebra import product,cols
from quadratic_centroid import zero_combinations
from quadratic_target import apply_basis, insert, reduce_vector


@dataclass(frozen=True)
class Certificate:
    leaves: tuple
    selector: int
    pairing: tuple
    method: str


def recover(n,m,constant,linear,pairs,*,selectors=None,max_pairing_trials=None):
    """Return a checked certificate, or None when the raw test is inconclusive."""
    if (n!=2*m or m<=0 or not 0<=constant<1<<m or len(linear)!=n or
        any(not 0<=v<1<<m for v in linear) or any(not (0<=i<j<n and 0<=v<1<<m)
                                                   for (i,j),v in pairs.items())):
        return None
    units=tuple(1<<i for i in range(n))
    def polar(h):
        cols=[0]*n
        for (i,j),value in pairs.items():
            if (value&h).bit_count()%2:
                cols[i] ^= 1<<j
                cols[j] ^= 1<<i
        return tuple(cols)
    polars=[polar(1<<i) for i in range(m)]
    if selectors is None:
        selectors=tuple(dict.fromkeys([1<<i for i in range(m)]+[(1<<m)-1]+
                                      [(1<<i)|(1<<j) for i,j in combinations(range(m),2)]))
    for h in selectors:
        if not 0<h<1<<m:
            raise ValueError("invalid scalar selector")
        b=polar(h)
        inverse={}
        for j,col in enumerate(b): insert(col,units[j],inverse)
        if len(inverse)!=n: continue
        ops=[tuple(reduce_vector(v,inverse)[1] for v in cols) for cols in polars]
        space={}
        basis=[]
        def record(x):
            if insert(x,0,space): basis.append(x)
        for a,c in combinations(ops,2):
            for i in range(n):
                record(apply_basis(a,c[i]) ^ apply_basis(c,a[i]))
        def candidate(seed,method):
            sub={}
            vectors=[]
            def add(x):
                if insert(x,0,sub): vectors.append(x)
            for v in seed: add(v)
            j=0
            while j<len(vectors) and len(vectors)<=m:
                for op in ops: add(apply_basis(op,vectors[j]))
                j+=1
            if len(vectors)!=m: return None
            pairing=check_pairing(n,m,constant,linear,pairs,vectors,max_trials=max_pairing_trials)
            return None if pairing is None else Certificate(tuple(vectors),h,pairing,method)
        check=candidate(basis,"commutators")
        if check: return check
        # Central nilpotents in the commutant can expose a self-extension
        # even when the induced generators on the quotient do not commute.
        enc=lambda a:sum(v<<(n*i) for i,v in enumerate(a))
        def centralizes(mat,generators):
            return sum((product(n,mat,g)^product(n,g,mat))<<(n*n*i)
                       for i,g in enumerate(generators))
        generators=[enc(a) for a in ops]
        comm=zero_combinations((1<<j for j in range(n*n)),lambda v:centralizes(v,generators))
        center=zero_combinations(comm,lambda v:centralizes(v,comm))
        def eventually_power(x):
            for _ in range((n-1).bit_length()): x=product(n,x,x)
            return x
        nil=zero_combinations(center,eventually_power)
        common=[]
        for x in nil:
            image=cols(n,x)
            check=candidate(image,"central nilpotent")
            if check: return check
            common.extend(image)
        check=candidate(common,"central nilpotent sum")
        if check: return check
    return None
