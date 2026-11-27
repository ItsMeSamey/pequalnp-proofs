"""Tiny minimax game and native NAND audit. Exponential evaluation is test-only."""
from functools import lru_cache
from unittest.mock import patch

import limited_query_halving as native
from check_binary_fault_solver import Source, raw
from forecast_consistency_search import threshold
from odd_masked_circuit import compile_source


@lru_cache(None)
def can_win(size,budget,m):
    if size == 0:
        return True
    if budget < 0:
        return False

    @lru_cache(None)
    def explore(zeros,ones):
        unknown = size-zeros-ones
        # If wrong, every uninspected point could have carried the opposite
        # label. A smaller budget then has to work on that entire set.
        for opposite in (zeros,ones):
            if can_win(opposite+unknown,budget-1,m):
                return True
        if unknown and zeros+ones < m:
            return explore(zeros+1,ones) and explore(zeros,ones+1)
        return False

    return explore(0,0)


def game():
    for m in range(1,9):
        for budget in range(5):
            c = native.capacity(m,budget)
            for size in range(1,19):
                assert (size <= c) == can_win(size,budget,m)
    for n in range(5):
        thresholds = [m for m in range(1,(1<<n)+1) if can_win(1<<n,n,m)]
        by_formula = [m for m in range(1,(1<<n)+1)
                      if native.capacity(m,n) >= 1<<n]
        assert min(thresholds) == (1 if n <= 1 else (1 << (n-1))+1)
        assert thresholds == by_formula and thresholds == list(range(min(thresholds),(1<<n)+1))


def nand_rows(n):
    for wire in range(n):
        yield (),wire
    for i in range(n):
        for j in range(n):
            yield ((i,j),),n
    c = Source(n)
    yield c.finish(c.xor(0,n-1))


def trajectories():
    for n in (1,2,3):
        for m in (1,2,3):
            for secret in range(1<<n):
                learner = native.LimitedQueryHalving(n,100,m)
                candidates = set(range(1<<n))
                genuine = candidates.copy()
                history = []
                for q in nand_rows(n):
                    sample = sorted(candidates)[:m]
                    valid = [x for x in sample if all(raw(n,h,x)==b for h,b in history)]
                    answer = raw(n,q,secret)
                    guess = int(2*sum(raw(n,q,x) for x in valid)>len(valid))
                    historical_cost = 0
                    for x in sample:
                        for h,b in history:
                            historical_cost += 1
                            if raw(n,h,x) != b:
                                break
                    assert learner.predict(q) == guess
                    assert learner.last_points == len(sample)
                    assert learner.last_query_evaluations == len(valid)
                    assert learner.last_history_evaluations == historical_cost
                    if guess:
                        assert learner.last_witness in valid and raw(n,q,learner.last_witness)
                    else:
                        assert learner.last_witness is None
                    assert learner.observe(q,answer) == (answer != guess)
                    if answer != guess:
                        history.append((q,answer))
                        candidates.difference_update(x for x in sample
                                                     if x not in valid or raw(n,q,x)!=answer)
                    genuine = {x for x in genuine if raw(n,q,x) == answer}
                    stored = set(learner.prefix) | set(range(learner.tail_start,1<<n))
                    assert tuple(history) == learner.history
                    assert stored == candidates and secret in genuine <= stored
                    assert (learner.remaining,learner.mistakes) == (len(stored),len(history))


def masked(supported):
    c = Source(3)
    uv = c.both(1,2)
    lower = c.both(c.both(c.inv(0),uv),-2 if supported else -1)
    upper = c.both(0,uv)
    out = c.nand(c.inv(lower),c.inv(upper))
    F = compile_source(3,c.finish(out))
    n = 12
    probe = threshold(n,3)
    calls = []
    def traced(width,gates,output,point):
        calls.append(((gates,output),point))
        assert len(calls) <= 5
        return raw(width,(gates,output),point)
    with patch.object(native,'evaluate',traced):
        learner = native.LimitedQueryHalving(n,200,2)
        assert raw(n,F,7)
        assert learner.predict(F) == 0 and learner.observe(F,1)
        assert calls == [(F,0),(F,1)]
        assert learner.predict(probe) == int(supported) and learner.last_points == 2
        expected = [(F,0),(F,1),(F,2),(F,3)]
        if supported:
            expected.append((probe,3))
        assert calls == expected
        assert learner.last_history_evaluations == 2
        assert learner.last_query_evaluations == int(supported)
        assert learner.current_evaluations == 2+int(supported)
        assert learner.history_evaluations == 2
        assert learner.point_evaluations == len(calls)
        assert learner.last_witness == (3 if supported else None)
        if supported:
            witness = learner.last_witness
            assert all(raw(n,q,witness) == b for q,b in learner.history)
            assert raw(n,probe,witness)
    assert [x for x in range(4) if raw(n,F,x)] == ([3] if supported else [])



def saturation():
    learner = native.LimitedQueryHalving(0,1,1)
    one = ((),-2)
    also_one = (((-1,-1),),0)
    assert one != also_one and raw(0,one,0) == raw(0,also_one,0) == 1
    limit = 1 << 8
    for i in range(limit+4):
        query = (one,also_one)[i%2]
        assert learner.predict(query) == 1
        assert not learner.observe(query,1)
        assert learner.current_evaluations == learner.point_evaluations == min(i+1,limit)
    assert learner.history == () and learner.history_evaluations == 0
    # An impossible label eliminates the only seed. Further opposite responses
    # cannot consume memory or evaluate even the sole raw original point.
    assert learner.observe(one,0)
    assert learner.remaining == 0
    frozen = (learner.history,learner.mistakes,learner.point_evaluations)
    for i in range(12):
        query = (one,also_one)[i%2]
        assert learner.predict(query) == 0 and learner.last_witness is None
        learner.observe(query,1)
        assert (learner.history,learner.mistakes,learner.point_evaluations) == frozen
        assert learner.remaining == learner.last_points == 0


if __name__ == '__main__':
    saturation()
    game()
    trajectories()
    masked(False)
    masked(True)
    print('Oracle game, history-filtered cohorts, physical point counts and positive witnesses agree.')
