"""Independent physical oracle and structural controls for Stage 4."""
import json
from itertools import combinations, product

import event_gaussian_solver
from check_event_tree_native import normalize, raw_key, run_machine
from padding_cnf import encode


def source_oracle(f):
    aliases = [normalize(value) for value in f['aliases']]
    names = sorted({name for name, _ in aliases})
    machine = tuple(f[k] for k in ('table', 'initial', 'bottom', 'outputs'))
    words = {}
    for bits in product(range(2), repeat=len(names)):
        values = dict(zip(names, bits))
        key = sum((values[name] ^ sign) << i for i, (name, sign) in enumerate(aliases))
        raw = encode(f['challenge'], f['n'], key)
        assert raw_key(raw, f['n']) == key
        out, _ = run_machine(machine, raw)
        words[raw] = (key, values, out)
    return words


def check_case(f, words, backend, occ=(), ids=(), want=None, **options):
    args = tuple(f[k] for k in ('challenge','n','aliases','table','initial','bottom','outputs'))
    occ = tuple(f.get('occurrence_pins', ())) + tuple(occ)
    ids = tuple(f.get('id_pins', ())) + tuple(ids)
    selected = {raw: v for raw, v in words.items()
                if all(((v[0] >> i) & 1) == b for i, b in occ)
                and all(v[1][name] == b for name, b in ids)}
    answer = event_gaussian_solver.solve(*args, backend=backend,
            schedule=f.get('schedule' if backend == 'raw' else 'macro_schedule'),
            occurrence_pins=occ, id_pins=ids, **options)
    if want == 'unknown':
        assert answer['status'] == 'unknown' and not answer['samples'], answer['status']
        return answer
    bits = {v[-1] for v in selected.values()}
    assert want is None or bits == want
    assert answer['status'] == ('empty','constant','pair')[len(bits)], (answer['status'],answer.get('reason'))
    assert [s['prediction'] for s in answer['samples']] == sorted(bits)
    for sample in answer['samples']:
        assert selected[sample['physical']] == (sample['key'],sample['underlying'],sample['prediction'])
    if len(bits) == 1:
        assert answer['value'] in bits
    assert answer['metrics']['replay_bytes'] == sum(len(s['physical']) for s in answer['samples'])
    return answer


def prove_clique_minor(chart, branches):
    edges = set(map(frozenset, chart.edges))
    used = set()
    for group in branches:
        assert group and used.isdisjoint(group)
        used.update(group)
        reached = {group[0]}
        while True:
            nxt = reached | {v for v in group if any(frozenset((v,w)) in edges for w in reached)}
            if nxt == reached:
                break
            reached = nxt
        assert reached == set(group)
    assert all(any(frozenset((u,v)) in edges for u in a for v in b)
               for a,b in combinations(branches,2))


def main():
    import event_macro
    from stage4_event_fixtures import affine_clique, record_codes
    from stage4_nonaffine import and_gate, codebooks

    f = affine_clique(5)
    args = tuple(f[k] for k in ('challenge','n','aliases','table','initial','bottom','outputs'))
    compiled = event_macro.build(*args, schedule=f['macro_schedule'])
    assert len(f['minor_slot_sets']) == 5
    prove_clique_minor(compiled, f['minor_slot_sets'])
    words = source_oracle(f)
    assert len(words) == 2048
    assert all(v[-1] == sum(v[1].values()) % 2 for v in words.values())
    metrics = {}
    for bit, key in [(0,2061057), (1,2060803)]:
        assert words[f['raw_witnesses'][bit]][::2] == (key, bit)
    for backend in ('macro', 'raw'):
        answer = check_case(f, words, backend, want={0,1}, codebooks=record_codes)
        g = answer['metrics']['gaussian']
        assert g['exception_count'] == 0 and g['branches'] == 0 and g['branch_states'] == 2
        metrics['clique-' + backend] = g
    for bit in (0,1):
        values = words[f['raw_witnesses'][bit]][1]
        check_case(f, words, 'macro', ids=tuple(values.items()), want={bit}, codebooks=record_codes)
    check_case(f, words, 'macro', ids=((1,0),), want=set(), codebooks=record_codes)
    limited = check_case(f, words, 'macro', want='unknown', branch_cap=0, codebooks=record_codes)
    assert limited['reason'] == 'branch cap'
    partial = event_gaussian_solver.solve(*args, backend='macro', codebooks=record_codes,
                schedule=f['macro_schedule'], occurrence_pins=f['occurrence_pins'], branch_cap=1)
    assert partial['status'] == 'unknown' and partial['reason'] == 'branch cap'
    sample, = partial['samples']
    assert words[sample['physical']] == (sample['key'], sample['underlying'], 0)
    assert all(((sample['key'] >> i) & 1) == b for i,b in f['occurrence_pins'])

    g = and_gate()
    original = source_oracle(g)
    assert {v[0]:v[-1] for v in original.values()} == {0:0,1:0,2:0,3:1}
    for cap in (0,3):
        refusal = check_case(g, original, 'macro', want='unknown', codebooks=codebooks, exception_cap=cap)
        assert refusal['reason'] == 'exception cap'
        assert refusal['metrics']['gaussian']['exception_count'] == 4
    ok = check_case(g, original, 'macro', want={0,1}, codebooks=codebooks, exception_cap=4)
    gm = ok['metrics']['gaussian']
    assert gm['exception_count'] == 4 and gm['nonaffine_factors'] == 1 and gm['branches'] > 0
    metrics['and-macro'] = gm
    check_case(g, original, 'macro', ids=((71,1),), want={0}, codebooks=codebooks)
    check_case(g, original, 'macro', ids=((71,0),(23,1)), want={1}, codebooks=codebooks)
    print(json.dumps(metrics, sort_keys=True))


if __name__ == '__main__':
    main()
