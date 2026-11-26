"""Compile signed CNF to width-five permutation instructions and find a witness."""
from functools import lru_cache
from heapq import heapify, heappop, heappush
from itertools import permutations

from cluster_pass_rail import decide_clusters
from commuting_toggle_rails import compose, inverse

IDENT = tuple(range(5))
RHO = (1,2,3,4,0)


def _is_cycle(p):
    x = p[0]
    length = 1
    while x:
        x = p[x]
        length += 1
    return length == 5


CYCLES = tuple(p for p in permutations(IDENT) if _is_cycle(p))


@lru_cache(maxsize=24)
def _commutator_pair(target):
    for a in CYCLES:
        for b in CYCLES:
            # Chronological sequence A,B,A^-1,B^-1.
            if compose(inverse(b),compose(inverse(a),compose(b,a))) == target:
                return a,b
    raise AssertionError("no five-cycle commutator")


def _inverse_program(program):
    return [(v,inverse(p),inverse(q)) for v,p,q in reversed(program)]


def _negate(program,target):
    result = _inverse_program(program)
    v,p,q = result[-1]
    result[-1] = (v,compose(target,p),compose(target,q))
    return result


def _tree(nodes,op):
    # Dyadic size buckets keep a long clause from acquiring needlessly large depth.
    heap = [(h,i,node) for i,(h,node) in enumerate(nodes)]
    heapify(heap)
    serial = len(heap)
    while len(heap)>1:
        _,_,left = heappop(heap)
        right_h,_,right = heappop(heap)
        heappush(heap,(right_h+1,serial,(op,left,right)))
        serial += 1
    h,_,node = heap[0]
    return h,node


def _compile(node,target):
    if isinstance(node,int):
        return [(node,IDENT,target)]
    op,left,right = node
    a,b = _commutator_pair(target)
    first = _compile(left,a)
    second = _compile(right,b)
    if op == "or":
        first,second = _negate(first,a),_negate(second,b)
    gates = first + second + _inverse_program(first) + _inverse_program(second)
    return _negate(gates,target) if op == "or" else gates


def compile_cnf(n,clauses):
    """Return (gates, fixed_tail). Before closing, true outputs RHO and false IDENT.
    Literals are signed, one-based. The fixed tail represents constant formulas.
    """
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid variable count")
    clauses = [tuple(c) for c in clauses]
    if any(not isinstance(lit,int) or not 1<=abs(lit)<=n for c in clauses for lit in c):
        raise ValueError("invalid signed literal")
    if any(not c for c in clauses):
        return [],IDENT
    if not clauses:
        return [],RHO
    clause_trees = [_tree([(0,lit) for lit in c],"or") for c in clauses]
    _,tree = _tree(clause_trees,"and")
    return _compile(tree,RHO),IDENT


def evaluate(gates,tail,mask):
    p = IDENT
    for lit,low,high in gates:
        value = ((mask>>(abs(lit)-1))&1) ^ (lit<0)
        p = compose(high if value else low,p)
    return compose(tail,p)


def find_witness(n,clauses):
    """Return (input mask, starting state) or None using cluster trace search over F₂."""
    gates,tail = compile_cnf(n,clauses)
    passes = [(True,[g]) for g in gates]
    closing = compose(inverse(RHO),tail)
    result,_,_ = decide_clusters(n,5,passes,range(1,n+1),[len(passes)] if passes else [],
                                 prime=2,closing=closing,promised_trace=True)
    return result
