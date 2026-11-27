"""Staged side-by-side comparison. Run here with GS on PYTHONPATH."""
import syndrome_range_forecast as syndrome
import tail_range_forecast as permutation
from check_binary_fault_solver import Source, raw
from forecast_consistency_search import threshold


def check(h):
    circuit = Source(h)
    # The last input reaches the output on two different XOR arms.
    a = circuit.xor(0,h-1)
    b = circuit.xor(1,h-1)
    q = circuit.finish(circuit.both(a,b))
    first = threshold(h,0)
    two = threshold(h,1)
    cap = max(len(row[0]) for row in (q,first,two))
    size = 1 << h
    for x in range(size):
        last = x & 1
        assert raw(h,q,x) == (((x >> (h-1)) ^ last) & (((x >> (h-2)) & 1) ^ last))
    simple = permutation.TailRangeForecast(h,cap,max_latents=4)
    low = syndrome.SyndromeRangeForecast(h,cap,max_latents=3)
    feasible = syndrome.SyndromeRangeForecast(h,cap,max_latents=4)
    for engine, cost in ((simple,size),(low,4)):
        result = engine.observe(q,1)
        assert result['reason'] == 'latent_budget' and result['required'] == cost
        assert engine.history == ()
    blocked = syndrome.SyndromeRangeForecast(h,len(q[0])-1,max_latents=4)
    assert blocked.observe(q,1)['reason'] == 'gate_budget' and blocked.history == ()

    history = ()
    replay = ()
    for i,(query,label) in enumerate(((first,0),(q,1),(two,1),(q,1))):
        groups = [set(),set()]
        for x in range(size):
            if all(raw(h,row,x) == b for row,b in history):
                groups[raw(h,query,x)].add(x)
        counts = tuple(map(len,groups))
        bit = int(counts[1] > counts[0])
        for module,limit in ((syndrome,4),(permutation,size)):
            result = module.posterior(h,history,query,max_latents=limit)
            assert result['status'] == 'exact' and result['counts'] == counts
            assert result['prediction'] == bit
            assert result['witness'] == result['witnesses'][bit]
            for group, witness in zip(groups,result['witnesses']):
                assert witness in group if group else witness is None
            if i == 1:
                assert counts == (3*size//4,size//4)
                width = 2 if module is syndrome else h
                assert result['latent_widths'] == (width,width)
        assert raw(h,query,1) == label
        assert feasible.predict(query) == syndrome.learner_factory(4)(h,cap,replay,query) == bit
        assert feasible.observe(query,label) == (bit != label)
        if bit != label:
            history += ((query,label),)
        replay += ((query,label),)
        assert feasible.history == history
    assert history == ((q,1),(two,1))


if __name__ == '__main__':
    for width in (4,7,10):
        check(width)
    print('Rank-two and permutation posteriors agree on original assignments.')
