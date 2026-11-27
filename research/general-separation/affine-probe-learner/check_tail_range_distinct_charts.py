"""Inspect the two charts actually used by posterior, using original-word labels."""
from unittest.mock import patch

import tail_range_forecast as engine
from check_exact_tail_masked_majority import fixture, raw_table
from forecast_consistency_search import threshold
from odd_masked_circuit import compile_source
from tail_permutation_range import recognize


def check(query, raw_bit, lo, hi, cuts, positive_offset, histogram):
    history = ((threshold(3, lo-1), 0), (threshold(3, hi), 1))
    states = []

    def capture(h, system):
        state = recognize(h, system)
        states.append(state)
        return state

    with patch.object(engine, 'recognize', capture):
        result = engine.posterior(3, history, query, max_latents=2)
    assert result['status'] == 'exact' and len(states) == 2
    assert result['counts'] == histogram
    assert result['prediction'] == int(histogram[1] > histogram[0])
    for bit, state in enumerate(states):
        assert state.cuts == (cuts[bit],) and state.m == 1
        expected = {x for x in range(lo,hi+1) if raw_bit(x) == bit}
        assert histogram[bit] == len(expected) == state.range_count(lo,hi)
        assert result['witnesses'][bit] in expected
        assert state.F == ((),0)
        lifted = set()
        for prefix in range(4):
            offset = positive_offset(prefix) ^ (1-bit)
            assert state.offset(prefix) == offset
            for y in (0,1):
                x = (prefix << 1) | (y ^ offset)
                assert state.lift(prefix,y) == x and state.project(x) == y
                assert (raw_bit(x) == bit) == bool(y)
                if y and lo <= x <= hi:
                    lifted.add(x)
        assert lifted == expected


def strict_masked(truth):
    m, h = 4, 16
    planted = (1 << m) - 1
    source = compile_source(m, fixture(0, truth))
    cutoff = threshold(h, planted)
    final = threshold(h, 1 << (m-1))
    queries = (source, cutoff, final)
    model = engine.TailRangeForecast(h, max(len(q[0]) for q in queries), max_latents=1 << m)
    copies = 1 << (3*m)
    models = 1 + 2*truth
    bins = (((1 << h)-copies*models, copies*models),
            ((copies-1)*models, models), (1, 2*truth))
    live = (1 << (1 << h)) - 1
    history = ()
    for i,(q,counts) in enumerate(zip(queries,bins)):
        mask = raw_table(h,q)
        groups = (live & ~mask, live & mask)
        assert tuple(group.bit_count() for group in groups) == counts
        assert counts[0] != counts[1]
        vote = int(counts[1] > counts[0])
        result = engine.posterior(h,history,q,max_latents=1 << m)
        assert result['status'] == 'exact' and result['counts'] == counts
        assert model.predict(q) == result['prediction'] == vote
        assert live >> planted & 1
        if i < 2:
            assert vote == 0 and mask >> planted & 1
            assert model.observe(q,1) is True
            history += ((q,1),)
            live = groups[1]
        else:
            assert vote == truth and not (mask >> planted & 1)
        assert model.history == history


def main():
    check(((),2), lambda x: x & 1, 0,2,(3,2),lambda u: 0,(2,1))
    # XOR of the first and last physical bits. Both offsets vary with the prefix.
    xor = (((0,2),(0,3),(2,3),(4,5)),6)
    check(xor,lambda x: ((x >> 2) ^ x) & 1, 1,5,(7,6),lambda u: u >> 1,(2,3))
    for truth in (0,1):
        strict_masked(truth)


if __name__ == '__main__':
    main()
