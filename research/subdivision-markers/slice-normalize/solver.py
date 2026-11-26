"""One affine marker on general square binary single-literal guard matrices."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from functools import lru_cache

@lru_cache(maxsize=1)
def load_alternating():
    for root in Path(__file__).resolve().parents:
        for suffix in ('pnp-research/research/two-markers/check.py','two-markers/check.py'):
            candidate = root / suffix
            if candidate.exists():
                spec = spec_from_file_location('two_markers', candidate)
                mod = module_from_spec(spec)
                spec.loader.exec_module(mod)
                return mod.witness
    raise ImportError('two-markers/check.py required')

def parity(a):
    return a.bit_count() % 2

def affine_chart(n, equations):
    """Return base, kernel basis and the actual free coordinate indices."""
    rows = [mask | bit<<n for mask,bit in equations]
    pivots = []
    for j in range(n):
        k = next((k for k in range(len(pivots),len(rows)) if rows[k]>>j&1),None)
        if k is None:
            continue
        i = len(pivots)
        rows[k],rows[i] = rows[i],rows[k]
        for r in range(len(rows)):
            if r != i and rows[r]>>j&1:
                rows[r] ^= rows[i]
        pivots.append(j)
    if any(rows[len(pivots):]):
        return None
    free = [j for j in range(n) if j not in pivots]
    def lift(bit):
        return sum(1<<j for i,j in enumerate(pivots) if rows[i]>>bit&1)
    return lift(n), [(1<<j)|lift(j) for j in free], free

def coefficients(M):
    n = len(M)
    return sum(((M[i]>>j&1) ^ ((M[j]>>i&1) if i!=j else 0)) << (i*n+j)
               for i in range(n) for j in range(i+1))

def normalize(M, equations, symmetric_only=False):
    """Find a guardwise-equivalent alternating/symmetric matrix, or None."""
    n = len(M)
    diagonal = sum(1 << (i*n+i) for i in range(n))
    def projection(v):
        return v & ~diagonal if symmetric_only else v
    pivots = {}
    edits = []
    for i in range(n):
        for mask,h in equations:
            delta = mask ^ (h << i)
            column = projection(sum(1<<(max(i,j)*n+min(i,j)) for j in range(n) if delta>>j&1))
            coeff = 1 << len(edits)
            edits.append((i,delta))
            while column:
                p = column.bit_length()-1
                if p not in pivots:
                    pivots[p] = column,coeff
                    break
                c,k = pivots[p]
                column ^= c
                coeff ^= k
    target = projection(coefficients(M))
    moves = 0
    while target:
        p = target.bit_length()-1
        if p not in pivots:
            return None
        c,k = pivots[p]
        target ^= c
        moves ^= k
    result = list(M)
    for j,(i,delta) in enumerate(edits):
        if moves>>j&1:
            result[i] ^= delta
    return result

def quadratic(M,x):
    return sum(parity(row&x) for i,row in enumerate(M) if x>>i&1)%2

def zero_branches(M,chart):
    """Return affine equations whose union is the zero set, or raise ValueError."""
    base,dirs,free = chart
    c = quadratic(M,base)
    lin = sum((quadratic(M,base^u)^c)<<i for i,u in enumerate(dirs))
    rows = [0]*len(dirs)
    for i,u in enumerate(dirs):
        for j in range(i):
            if quadratic(M,base^u^dirs[j]) ^ c ^ (lin>>i&1) ^ (lin>>j&1):
                rows[i] |= 1<<j
                rows[j] |= 1<<i
    def ambient(mask):
        return sum(1<<j for k,j in enumerate(free) if mask>>k&1)
    if not any(rows):
        return [(ambient(lin), c)] if lin or not c else []
    p = next(v for v in rows if v)
    q = next(v for v in rows if v not in (0,p))
    if any(v not in (0,p,q,p^q) for v in rows):
        raise ValueError('outside affine/product class')
    remainder = lin ^ (p&q)
    for a in (0,1):
        for b in (0,1):
            if remainder == (a*q)^(b*p) and c == a*b:
                return [(ambient(p),a),(ambient(q),b)]
    raise ValueError('outside affine/product class')

def witness(M,marker,target):
    """Return witness mask, None for infeasible, or raise ValueError outside class."""
    n = len(M)
    original = [(marker,target)]
    chart = affine_chart(n,original)
    if chart is None:
        return None
    for equation in zero_branches(M,chart):
        equations = original+[equation]
        if affine_chart(n,equations) is None:
            continue
        graph = normalize(M,equations)
        assert graph is not None
        labels = [sum((m>>i&1)<<j for j,(m,h) in enumerate(equations)) for i in range(n)]
        syndrome = sum(h<<j for j,(m,h) in enumerate(equations))
        x = load_alternating()(graph,labels,syndrome)
        if x is not None:
            return x
    return None
