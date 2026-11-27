"""Stage 5 preregistered native controls for projection and signed intersections."""
from collections import Counter as Census
from itertools import product
import json

from check_event_tree_native import normalize, raw_key, run_machine
from compressed_ie import Counter
from event_compressed_solver import solve as compressed
from event_flat_solver import solve as projected
from event_rank2_solver import solve as fourier
from padding_cnf import encode


def physical(f, codes, occ=(), ids=()):
    aliases = [normalize(a) for a in f['aliases']]
    occ = tuple(f.get('occurrence_pins', ())) + tuple(occ)
    ids = tuple(f.get('id_pins', ())) + tuple(ids)
    names = sorted({name for name, _ in aliases})
    machine = tuple(f[k] for k in ('table', 'initial', 'bottom', 'outputs'))
    words = {}
    for bits in product((0, 1), repeat=len(names)):
        values = dict(zip(names, bits))
        key = sum((values[name] ^ sign) << i for i, (name, sign) in enumerate(aliases))
        if any(((key >> i) & 1) != b for i,b in occ) or any(values[name] != b for name,b in ids):
            continue
        word = encode(f['challenge'], f['n'], key)
        assert raw_key(word, f['n']) == key
        out, _ = run_machine(machine, word)
        words[word] = (key, values, out)
    args = (f['challenge'], f['n'], f['aliases'], *machine)
    opts = dict(backend='macro', schedule=f['macro_schedule'], codebooks=codes,
                occurrence_pins=occ, id_pins=ids)
    return words, args, opts


def check(fn, data, *, expected=None, refusal=None, **limits):
    words, args, opts = data
    counts = dict.fromkeys((0,1),0)
    counts.update(Census(v[-1] for v in words.values()))
    if expected is not None:
        assert counts == expected, counts
    a = fn(*args, **opts, **limits)
    for sample in a['samples']:
        assert words[sample['physical']] == (sample['key'],sample['underlying'],sample['prediction'])
    if refusal:
        assert a['status']=='unknown' and 'counts' not in a, (a['status'], a.get('reason'))
        assert refusal in a['reason'], a['reason']
    else:
        actual = {b for b,n in counts.items() if n}
        assert a['status'] == ('empty','constant','pair')[len(actual)], a.get('reason')
        assert {s['prediction'] for s in a['samples']} == actual
        assert len(a['samples']) == len(actual)
        if len(actual) == 1:
            assert a['value'] in actual
        if fn in (compressed,fourier):
            assert a['counts'] == counts
        else:
            assert 'counts' not in a
    return a['metrics']['gaussian']


def growing_intersections():
    rows = []
    for k in (4,8,16,32):
        holes = [((1 << j)-1,0) for j in range(1,k+1)]
        c = Counter(k, [], holes)
        assert c.count()[0] == 1 << (k-1)
        assert c.count(1,0)[0] == 0 and c.count(1,1)[0] == 1 << (k-1)
        word = c.witness()
        assert word is not None and all(word & mask != value for mask,value in holes)
        m = c.metrics
        assert m['projected_cylinders']==k and m['final_states']==2 and m['peak_states']<=3
        rows.append((k,m['peak_states'],m['work']))
    independent = Counter(11, [], [(3 << (2*i),0) for i in range(5)])
    for value in (0,1):
        assert independent.count(1<<10,value<<10)[0] == 3**5
    assert independent.metrics['final_states']==32
    return rows


def projections():
    from event_affine_flat import projected_solve
    def test(n, eqs, holes, **opts):
        feasible = {word for word in range(1<<n)
                    if all((word & mask).bit_count()%2 == rhs for mask,rhs in eqs)
                    and all(word & mask != value for mask,value in holes)}
        a = projected_solve(n,eqs,holes,**opts)
        if a['status'] == 'sat':
            assert a['word'] in feasible
        elif a['status'] == 'unsat':
            assert not feasible
        else:
            assert a['status'] == 'unknown' and 'word' not in a
        return a
    projected_two = test(5,[(7,0)],[(7,0),(7,1)])
    assert projected_two['status']=='sat'
    m = projected_two['metrics']
    assert m['cover_calls']==1 and m['residual_rank']==2 and m['dropped']>=1
    assert test(3,[(7,0)],[(7,0)],dimension_cap=1)['status']=='unknown'
    assert test(3,[],[(7,0)])['status']=='unknown'
    assert test(3,[],[(7,0)],max_flat_rank=None)['status']=='sat'
    propagated = test(3,[],[(3,0),(3,3),(4,0)])
    assert propagated['status']=='sat' and propagated['metrics']['parallel_groups']>0
    assert test(3,[],[(3,i) for i in range(4)])['status']=='unsat'
    return m


def generic_counts():
    from event_compressed_ie import solve
    from ie_merge_controls import cases, brute_counts
    for name,domains,constraints,out,expected in cases():
        assert brute_counts(domains,constraints,out) == expected
        result = solve(domains,constraints,out)
        assert result['counts']==expected, name
        for bit,assignment in result['witnesses'].items():
            assert all(assignment[v] in d for v,d in domains.items())
            assert assignment[out]==bit
            assert all((assignment[u],assignment[v]) in rel for u,v,rel in constraints)


def physical_gate():
    from stage4_nonaffine import and_gate, codebooks
    f = and_gate()
    data = physical(f,codebooks)
    expected = {0:3,1:1}
    m = check(compressed,data,expected=expected)
    proj = check(projected,data,expected=expected)
    assert proj['queries'][0]['cover_calls'] == 1
    assert proj['queries'][1]['parallel_groups'] >= 1
    check(compressed,data,refusal='state cap',state_cap=0)
    check(compressed,data,refusal='work cap',work_cap=0)
    for fn in (projected,compressed,fourier):
        check(fn,data,refusal='omission cap',omission_cap=3)
        check(fn,physical(f,codebooks,ids=[(71,1)]),expected={0:2,1:0})
        check(fn,physical(f,codebooks,occ=[(0,0),(0,1)]),expected={0:0,1:0})
    check(projected,data,refusal='dimension cap',dimension_cap=0)
    return m


def fourier_controls():
    from projected_rank2_fourier import count_witness
    from stage4_nonaffine import and_gate, codebooks
    from stage4_event_fixtures import affine_clique, record_codes
    flats = [((1,0),(2,1)),((3,1),(4,0))]
    allowed = {w for w in range(32) if all(any((mask&w).bit_count()%2 != b for mask,b in f)
                                             for f in flats)}
    count, witness, metrics = count_witness(5,flats,codimension_cap=1)
    assert count == len(allowed) and witness in allowed
    assert metrics['syndrome_rank'] == 1 and metrics['fiber_dimension'] == 2
    assert count_witness(5,flats,codimension_cap=0)[:2] == (None,None)
    check(fourier,physical(and_gate(),codebooks),expected={0:3,1:1})
    f = affine_clique(5)
    words,args,opts = physical(f,record_codes)
    opts.update(backend='raw',schedule=f['schedule'])
    raw_metrics = check(fourier,(words,args,opts),expected={0:256,1:256},codimension_cap=0)
    assert all(q['ambient_fiber_dimension'] == 8 for q in raw_metrics['queries'].values())
    return metrics


def partial_rank_refusal():
    from event_rank2_fourier import solve
    domains = {'x':tuple(range(8)), 'bit':(0,1)}
    allowed = set(product(domains['x'],domains['bit'])) - {(0,0)}
    result = solve(domains,[('x','bit',allowed)],'bit')
    assert result['status'] == 'unknown' and 'counts' not in result
    assert result['reason'] == 'projected rank exceeds two'
    assert set(result['witnesses']) == {1}
    witness = result['witnesses'][1]
    assert (witness['x'], witness['bit']) in allowed and witness['bit'] == 1


def comparator_control(d, payload):
    from event_ie_solver import solve as old
    from stage5_comparator import comparator_fixture
    f = comparator_fixture(d,payload)
    data = physical(f,f['record_codes'])
    expected = {b:1 << (2*d+payload-1) for b in (0,1)}
    for b,raw in f['raw_witnesses'].items():
        assert data[0][raw][2] == b
    bound = 1 + 3 * 4**d
    metrics = check(compressed,data,expected=expected,state_cap=bound)
    assert metrics['peak_states'] <= bound and metrics['cylinders'] >= 4**d
    check(old,data,refusal='branch cap',branch_cap=bound)
    return {k:metrics[k] for k in ('projected_cylinders','cylinders','peak_states',
                                    'final_states','work')}


def main():
    generic_counts()
    partial_rank_refusal()
    report = dict(growing=growing_intersections(), projection=projections(),
                  physical_and=physical_gate(), fourier=fourier_controls(),
                  comparator=comparator_control(1,3))
    print(json.dumps(report,sort_keys=True))


if __name__ == '__main__':
    main()
