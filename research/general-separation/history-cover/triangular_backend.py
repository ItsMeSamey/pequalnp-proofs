"""Eliminate triangular producer variables before bounded-rank character counting."""
from quadratic_parse import parse
from character_backend import backend as characters
from cover import System


def encode(f):
    return [tuple(2<<i for i in range(m.bit_length()) if m>>i&1) for m in sorted(f)]


def backend(system,max_rank):
    _,forms=parse(system)
    active=[forms[-1]]
    retained=[]
    for (symbol,_),equation in reversed(list(zip(system.definitions,forms[:-1]))):
        bit=symbol>>1
        rhs=equation^{bit}
        transformed=[]
        admissible=True
        for f in active:
            result={m for m in f if not m&bit}
            for m in f:
                if m&bit:
                    for term in rhs:
                        result.symmetric_difference_update([(m^bit)|term])
            if any(m.bit_count()>2 for m in result):
                admissible=False
                break
            transformed.append(result)
        if admissible:
            active=transformed
        else:
            active.append(equation)
            retained.append(bit)
    # Every active non-output row still defines its corresponding retained bit.
    # Reindex in original definition order. Checkpoint bits need not use numeric order.
    mapping={b:1<<(system.n+i) for i,b in enumerate(reversed(retained))}
    def rename(f):
        out=set()
        for m in f:
            h=m&((1<<system.n)-1)
            for b,v in mapping.items():
                if m&b:
                    h|=v
            assert m & ~((1<<system.n)-1) == sum(b for b in mapping if m&b)
            out.add(h)
        return out
    definitions=[(2*mapping[b],encode(rename(f^{b})))
                 for b,f in reversed(list(zip(retained,active[1:])))]
    reduced=System(system.n,definitions,encode(rename(active[0])^{0}))
    counter=characters(reduced,max_rank)
    def count(request,pins,assignment):
        if request is not system:
            raise ValueError('wrong query system')
        return counter(reduced,pins,assignment)
    count.rank=counter.rank
    count.retained=len(retained)
    return count
