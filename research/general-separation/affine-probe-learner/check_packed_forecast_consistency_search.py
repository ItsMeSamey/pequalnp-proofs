"""Original-word tests for tagged search, with a fixed deterministic finite oracle."""
from functools import lru_cache
from packed_forecast_consistency_search import decide, parameters, solve, tagged
from check_binary_fault_solver import Source, raw


def bind(F,i,b):
    def sub(w):
        return -1-b if w == i else w
    return tuple((sub(a),sub(b)) for a,b in F[0]),sub(F[1])


def fixture(C,early):
    n = 2
    c = Source(n)
    F = c.finish(c.both(c.inv(0),1))  # unique witness 01
    plan = parameters(n,len(F[0]),C,0)
    k = plan['k']
    assert k == (2 if early else 1)
    width = n+k
    zero = bind(F,0,0)
    last = bind(zero,1,0)
    roots = {}
    for phase,form in enumerate((F,zero,last)):
        for tag in range(1<<k):
            q = tagged(n,form,k,tag)
            roots[q] = phase,tag
            assert len(q[0]) == plan['packed_gates']
            for u in range(1<<width):
                assert raw(width,q,u) == (raw(n,form,u>>k) and (u % (1<<k)) == tag)
    bad = tagged(n,zero if early else F,k,0)
    initial = tagged(n,F,k,0)
    @lru_cache(None)
    def row(q):
        return sum(raw(width,q,x) << x for x in range(1<<width))
    full = (1 << (1<<width))-1
    exceptions = row(bad)
    assert exceptions.bit_count() == C and not exceptions & 1
    resets, histories = [],[]
    def vote(history,query):
        live = full
        for q,y in history:
            live &= row(q) if y else ~row(q)
        if not history and early and query == initial:
            return 1
        if history == ((bad,1),):
            # Every surviving word here is in the designated exceptional set.
            assert live == exceptions
            return int(bool(row(query)&1))
        return int(2*(row(query)&live).bit_count() > live.bit_count())
    def learner(w,cap,history,query):
        assert (w,cap) == (width,plan['cap'])
        for i,(q,y) in enumerate(history):
            assert vote(history[:i],q) != y
        if history:
            histories.append(history)
        else:
            resets.append(roots[query])
        return vote(history,query)
    assert decide(n,F,learner,C,0)
    assert resets == ([(0,0)] if early else [(0,0),(0,1)])
    resets.clear()
    histories.clear()
    answer = solve(n,F,learner,C,0)
    assert answer['status'] == 'witness' and answer['assignment'] == 1
    assert raw(n,F,answer['assignment'])
    expected = ([(0,0),(1,0),(1,1)] if early else [(0,0),(0,1),(1,0)])
    expected += [(2,t) for t in range(1<<k)]
    assert resets == expected and answer['trials'] == len(expected)
    assert answer['decisions'] == 3 and answer['cap'] == plan['cap']
    assert ((bad,1),) in histories
    if early:
        assert all(not raw(n,F,x) for x in (2,3))
        assert ((initial,1),) not in histories


if __name__ == '__main__':
    fixture(1,False)
    fixture(2,True)
    print('Packed cap, disjoint rescue trials and original witness agree.')
