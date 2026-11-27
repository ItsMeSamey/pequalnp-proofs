"""Physical-word audit of candidate-preserving interval repairs."""
from primitive_rewrite_chain import endpoint, public_cap
from state_dependent_interval_repair import solve


def raw(n, formula, x):
    gates,output = formula
    values = {i:(x >> (n-i-1)) & 1 for i in range(n)}
    values.update({-1:0,-2:1})
    for wire,(left,right) in enumerate(gates,n):
        values[wire] = 1-(values[left]*values[right])
    return values[output]


def trial(n,formula,bound,corrupt=False):
    size = 1 << n
    cap = public_cap(n,len(formula[0]))
    endpoints = [endpoint(n,*formula,j) for j in range(-1,size)]
    witnesses = [x for x in range(size) if raw(n,formula,x)]
    for j,query in enumerate(endpoints,-1):
        assert len(query[0]) <= cap
        assert all(raw(n,query,x) == (x <= j and x in witnesses) for x in range(size))
    calls = []

    def forecast(history,query):
        if corrupt and not history:
            # One arbitrary phase until first mistake, then ordinary halving.
            return int(query in (endpoints[3],endpoints[4]))
        pool = [x for x in range(size) if all(raw(n,q,x) == label for q,label in history)]
        return int(2*sum(raw(n,query,x) for x in pool) > len(pool))

    def learner(width,budget,history,query):
        assert width == n and budget == cap
        for k,(past,label) in enumerate(history):
            assert forecast(history[:k],past) != label
        calls.append((history,query))
        return forecast(history,query)

    result = solve(n,formula,cap,bound,learner)
    assert result['forecasts'] == len(calls)
    assert result['replay_rounds'] == sum(len(h) for h,_ in calls)
    assert result['status'] == ('witness' if witnesses else 'unsat')
    if witnesses:
        assert result['assignment'] in witnesses
    if corrupt:
        # Top-level false crossing j=2 yields occupied integer intervals
        # [0,1] and [3,3], with different mistaken histories.
        assert size == 4 and 2 not in witnesses and len(witnesses) == 1
        assert endpoints[2] != endpoints[3]
        assert [query for h,query in calls if not h] == [
            endpoints[0], endpoints[4], endpoints[2], endpoints[3]]
        assert result['binary_forks'] >= 1 and result['ambiguity_depth'] >= 1
        left = ((endpoints[2],1),)
        right = ((endpoints[3],0),)
        assert any(h == left for h,_ in calls)
        if witnesses == [3]:
            assert any(h == right for h,_ in calls)
        assert result['assignment'] == witnesses[0]
    return result


if __name__ == '__main__':
    # Two two-bit NAND formulas accept only 01 and only 11 respectively.
    trial(2,(((0,0),(2,1),(3,3)),4),3,True)
    trial(2,(((0,1),(2,2)),3),3,True)
    # At zero dimension prediction is exact on every realizable stream.
    yes = trial(0,((),-2),0)
    no = trial(0,((),-1),0)
    assert (yes['nodes'],yes['forecasts'],yes['endpoint_errors']) == (1,2,0)
    assert (no['nodes'],no['forecasts'],no['endpoint_errors']) == (2,2,1)
    for n in (1,2,3):
        trial(n,((),-1),n)
        for wire in range(n):
            trial(n,((),wire),n)
    print('Both repairs, original witnesses, and interval-solver counters agree.')
