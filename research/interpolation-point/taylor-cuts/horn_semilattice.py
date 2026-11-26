"""Exact sparse GF(2) indicators on a Horn model family."""
from dataclasses import dataclass
from horn_closure_xor import _closure, _rules


class SupportBudgetExceeded(ValueError):
    """The running support, including a partial XOR accumulator, exceeded its cap."""


@dataclass(frozen=True)
class HornResidual:
    support: frozenset
    witness: int | None
    peak: int
    closure_queries: int


def _bits(mask):
    while mask:
        bit=mask & -mask
        yield bit
        mask ^= bit


def compile_horn_residual(n,horn_clauses,clauses=(),xor_rows=(),*,max_support=None):
    """Return the canonical GF(2) support and an actual model, or witness None.

    Horn and residual CNF lists use signed 1-based DIMACS literals. XOR rows
    are (mask,rhs). Process XOR rows in input order, then residual clauses.
    peak includes temporary supports while accumulating terms.
    """
    rules=_rules(n,horn_clauses)
    if max_support is not None and (not isinstance(max_support,int) or max_support<0):
        raise ValueError("invalid support cap")
    extra=[]
    for clause in clauses:
        pos=neg=0
        for lit in clause:
            if not isinstance(lit,int) or not 1<=abs(lit)<=n:
                raise ValueError("invalid residual literal")
            if lit>0:
                pos |= 1<<(lit-1)
            else:
                neg |= 1<<(-lit-1)
        if not pos & neg:
            extra.append((pos,neg))
    xors=tuple(xor_rows)
    for mask,b in xors:
        if not isinstance(mask,int) or not 0<=mask<1<<n or b not in (0,1):
            raise ValueError("invalid XOR equation")
    cache={}
    peak=0
    def close(seed):
        if seed not in cache:
            cache[seed]=_closure(rules,seed)
        return cache[seed]
    def observe(s):
        nonlocal peak
        peak=max(peak,len(s))
        if max_support is not None and len(s)>max_support:
            raise SupportBudgetExceeded("running support exceeds max_support")
    def toggle(s,c):
        if c is None:
            return
        if c in s:
            s.remove(c)
        else:
            s.add(c)
            observe(s)
    def multiply_variable_into(out,src,bit):
        for c in src:
            toggle(out,close(c|bit))
    base=close(0)
    support=set() if base is None else {base}
    observe(support)
    for mask,b in xors:
        if not support:break
        out=set() if b else support.copy()
        for bit in _bits(mask):
            multiply_variable_into(out,support,bit)
        support=out
    for pos,neg in extra:
        if not support:break
        # First apply all mandatory x_i factors at once to the violation term.
        bad=set()
        for c in support:
            toggle(bad,close(c|neg))
        for bit in _bits(pos):
            prev=bad
            bad=prev.copy()
            multiply_variable_into(bad,prev,bit)
            if not bad:break
        for c in bad:
            toggle(support,c)
    witness=min(support,key=lambda c:(c.bit_count(),c)) if support else None
    if witness is not None:
        assert all(a & witness != a or bool(witness & head) for a,head in rules)
        assert all((witness & pos) or (neg & ~witness) for pos,neg in extra)
        assert all((witness & m).bit_count()%2==b for m,b in xors)
    return HornResidual(frozenset(support),witness,peak,len(cache))


def solve_horn_semilattice(n,horn_clauses,clauses=(),xor_rows=(),*,max_support=None):
    """Return a satisfying bitmask or None; a budget refusal raises an exception."""
    return compile_horn_residual(n,horn_clauses,clauses,xor_rows,max_support=max_support).witness
