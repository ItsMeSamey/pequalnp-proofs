"""Bounded differential tests using original-coordinate bit-parallel NAND tables."""
from functools import lru_cache

from check_sampled_forecast_sat import mask_fixture
from forecast_consistency_search import threshold
from tail_range_forecast import TailRangeForecast, learner_factory, posterior


@lru_cache(None)
def inputs(h):
    size = 1 << h
    full = (1 << size) - 1
    wires = []
    for i in range(h):
        stride = 1 << (h-1-i)
        wires.append((full // ((1 << (2*stride)) - 1)) * (((1 << stride)-1) << stride))
    return full, tuple(wires)


@lru_cache(None)
def table(h, q):
    full, columns = inputs(h)
    wires = {-1:0, -2:full, **dict(enumerate(columns))}
    for index, (a,b) in enumerate(q[0],h):
        wires[index] = full ^ (wires[a] & wires[b])
    return wires[q[1]]


def exact(h, rows, q, budget=None):
    full, _ = inputs(h)
    live = full
    for row, b in rows:
        live &= table(h,row) if b else full ^ table(h,row)
    mask = table(h,q)
    subsets = live & (full ^ mask), live & mask
    expected = tuple(s.bit_count() for s in subsets)
    res = posterior(h,rows,q,max_latents=budget)
    assert res['status'] == 'exact' and res['counts'] == expected
    assert res['prediction'] == int(expected[1] > expected[0])
    for subset, w in zip(subsets,res['witnesses']):
        if subset:
            assert type(w) is int and 0 <= w < 1 << h and subset >> w & 1
        else:
            assert w is None
    assert res['witness'] == res['witnesses'][res['prediction']]
    return res


def small():
    h = 3
    full = ((),-2)
    thresholds = tuple(threshold(h,j) for j in range(-1,8))
    for j,q in enumerate(thresholds,-1):
        assert table(h,q) == (1 << (j+1))-1
    q = thresholds[4]
    gates,out = q
    alias = gates + ((out,out),(h+len(gates),h+len(gates))), h+len(gates)+1
    assert alias != q and table(h,alias) == table(h,q)
    arbitrary = (((1,2),(0,3)),4)
    for rows in ((), ((q,0),), ((q,1),(q,0)), ((q,1),(alias,1)),
                 ((q,0),(alias,1)), ((arbitrary,1),(thresholds[2],0)),
                 ((thresholds[0],1),), ((thresholds[-1],0),)):
        for probe in (q,alias,arbitrary,full):
            exact(h,rows,probe)
    assert exact(0,(),full)['counts'] == (0,1)

    # Reversing input order physically moves a one-coordinate test from the
    # rightmost to the leftmost wire; its unrestricted truth count is unchanged.
    late,early = ((),h-1),((),0)
    assert exact(h,(),late)['latent_widths'] == (1,1)
    assert exact(h,(),early)['latent_widths'] == (h,h)
    for probe in (early,late):
        exact(h,((threshold(h,1),1),),probe)
    assert table(h,early) & 3 == 0 and table(h,late) & 3 == 2
    assert posterior(h,(),early,max_latents=7)['required'] == 8
    exact(h,(),early,8)

    model = TailRangeForecast(h,0,max_latents=2)
    assert model.predict(early)['reason'] == 'latent_budget'
    assert model.observe(early,1)['reason'] == 'latent_budget'
    assert model.observe(arbitrary,0)['reason'] == 'gate_budget'
    assert model.history == ()
    assert model.predict(late) == 0 and model.observe(late,0) is False
    assert model.history == ()
    assert model.observe(late,1) is True and model.history == ((late,1),)
    assert model.predict(late) == 1
    replay = learner_factory(max_latents=2)
    assert replay(h,0,((late,0),(late,1)),late) == 1
    assert replay(h,0,((arbitrary,1),),late)['reason'] == 'gate_budget'


def masked():
    h = 12
    for phi in (False,True):
        source = mask_fixture(phi)
        secret = 3 if phi else 7
        assert table(h,source) >> secret & 1
        rows = ()
        stream = [source] + [threshold(h,(1 << j)-1) for j in range(11,2,-1)]
        model = TailRangeForecast(h,max(len(q[0]) for q in stream),max_latents=8)
        for q in stream:
            assert table(h,q) >> secret & 1
            res = exact(h,rows,q,8)
            assert res['prediction'] == model.predict(q) == 0
            assert model.observe(q,1) is True
            rows += ((q,1),)
            assert model.history == rows
        pivot = exact(h,rows,threshold(h,3),8)
        assert pivot['counts'] == ((1,1) if phi else (1,0))
        if phi:
            assert model.observe(threshold(h,3),1) is True


if __name__ == '__main__':
    small()
    masked()
    print('Tail forecast raw bins, witnesses, actual mistakes and cap controls passed.')
