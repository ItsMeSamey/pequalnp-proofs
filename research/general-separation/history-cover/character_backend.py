"""Count grouped systems with a bounded quadratic character rank."""
from quadratic_parse import parse, affine_domain, gauss, Unsupported


def backend(system, max_rank):
    if max_rank < 0:
        raise ValueError('negative rank budget')
    N,forms = parse(system)
    pivots = {}
    eq = []
    for form in forms:
        form = set(form)
        while True:
            pivot = max((m for m in form if m.bit_count()==2), default=None)
            if pivot is None:
                eq.append((sum(form-{0}),int(0 in form)))
                break
            if pivot not in pivots:
                if len(pivots) >= max_rank:
                    raise Unsupported('quadratic character rank exceeds budget')
                pivots[pivot] = form
                break
            form ^= pivots[pivot]

    def count(request, pins, assignment):
        if request is not system or pins < 0 or pins >> system.n or assignment < 0 or assignment & ~pins:
            raise ValueError('invalid query')
        extra = [(1<<i,(assignment>>i)&1) for i in range(system.n) if pins>>i&1]
        flat = affine_domain(N,eq+extra)
        if flat is None:
            return 0
        origin,dirs,_ = flat
        d = len(dirs)
        phases = []
        for f in pivots.values():
            def ev(x):
                return sum(x&m==m for m in f)&1
            c = ev(origin)
            linear = [ev(origin^v)^c for v in dirs]
            pairs = {(i,j) for j in range(d) for i in range(j)
                     if ev(origin^dirs[i]^dirs[j])^c^linear[i]^linear[j]}
            phases.append((c,sum(bit<<i for i,bit in enumerate(linear)),pairs))
        # Consecutive Gray characters toggle phase at index v2(step).
        bias = 1<<d
        c = lin = 0
        pairs = set()
        for step in range(1,1<<len(phases)):
            z,b,p = phases[(step & -step).bit_length()-1]
            c ^= z
            lin ^= b
            pairs ^= p
            bias += gauss(d,(c,lin,pairs))
        den = 1<<len(phases)
        assert bias % den == 0
        return bias//den
    count.rank = len(pivots)
    return count
