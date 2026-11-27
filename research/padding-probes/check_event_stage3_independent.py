"""Independent Stage 3 control on two concatenated physical ladders."""
from itertools import combinations
import json

import event_auto
import event_block_solver
import event_blocks
import event_csp
import event_macro
from check_event_tree_native import source_words
from stage3_event_fixtures import block_ladders


def connected(vertices, edges):
    vertices = set(vertices)
    assert vertices
    adjacency = {v: set() for v in vertices}
    for u, v in edges:
        if u in vertices and v in vertices:
            adjacency[u].add(v)
            adjacency[v].add(u)
    visited = set()
    todo = [next(iter(vertices))]
    while todo:
        v = todo.pop()
        if v not in visited:
            visited.add(v)
            todo.extend(adjacency[v] - visited)
    return visited == vertices


def validate_tree(vertices, graph_edges, bags, links):
    nodes = set(range(len(bags)))
    assert all(u in nodes and v in nodes and u != v for u, v in links)
    assert len(links) == len(bags) - 1 and connected(nodes, links)
    assert all(len(set(bag)) == len(bag) <= 4 for bag in bags)
    assert set().union(*map(set, bags)) == set(vertices)
    for v in vertices:
        assert connected((i for i, bag in enumerate(bags) if v in bag), links)
    for u, v in graph_edges:
        assert any(u in bag and v in bag for bag in bags)


def check_minors(fixture, edges):
    edges = {frozenset(edge) for edge in edges}
    used = set()
    for minor in fixture['minor_slot_sets']:
        assert len(minor) == 4
        for branch in minor:
            assert used.isdisjoint(branch) and connected(branch, edges)
            used.update(branch)
        for left, right in combinations(minor, 2):
            assert any(frozenset((u, v)) in edges for u in left for v in right)
    assert len(fixture['minor_slot_sets']) == 2


def check_result(answer, words, expected):
    assert answer['status'] == expected, (expected, answer.get('reason'))
    bits = {value[-1] for value in words.values()}
    assert bits == {sample['prediction'] for sample in answer['samples']}
    assert len(answer['samples']) == len(bits)
    for sample in answer['samples']:
        assert words[sample['physical']] == (sample['key'], sample['underlying'], sample['prediction'])
    if expected == 'constant':
        assert bits == {answer['value']}
    metrics = answer['metrics']
    assert metrics['replay_bytes'] == sum(len(x['physical']) for x in answer['samples'])
    if bits:
        assert metrics['width'] == 3 and len(metrics['apexes']) >= 2
        assert metrics['states'] == metrics['bag_row_bound'] > 0
        assert metrics['steps'] >= metrics['states']
    return {k: metrics[k] for k in ('blocks','width','states','steps','replay_bytes')}


def main():
    f = block_ladders(2, 3)
    args = tuple(f[k] for k in ('challenge','n','aliases','table','initial','bottom','outputs'))
    base = tuple(f['occurrence_pins'])
    words, height = source_words(*args[:3], args[3:], base, ())
    assert height == 2
    for bit, key in [(1,5851),(0,5842)]:
        assert words[f['raw_witnesses'][bit]][::2] == (key, bit)
    summaries = {}
    for backend, builder in [('raw', event_csp), ('macro', event_macro)]:
        schedule = f['schedule' if backend == 'raw' else 'macro_schedule']
        chart = builder.build(*args, schedule=schedule)
        if backend == 'raw':
            validate_tree(chart.domains, chart.edges, f['bags'], f['tree_edges'])
            for edge in f['bridges']:
                others = [e for e in chart.edges if set(e) != set(edge)]
                assert len(others) + 1 == len(chart.edges)
                assert not connected(chart.domains, others)
        else:
            check_minors(f, chart.edges)
        tree = event_blocks.decompose(chart.domains, chart.edges)
        assert tree['status'] == 'ok' and tree['width'] == 3
        validate_tree(chart.domains, chart.edges, tree['bags'], tree['tree_edges'])
        options = dict(backend=backend, schedule=schedule, occurrence_pins=base)
        global_answer = event_auto.solve(*args, **options)
        assert global_answer['status'] == 'unknown' and not global_answer['samples']
        assert global_answer['metrics']['decomposition_attempts'] == len(chart.domains) + 1
        cases = [('pair', (), (), 'pair'), ('zero', ((0, 0),), (), 'constant'),
                 ('one', (), ((1009, 1), (1120, 0)), 'constant'),
                 ('conflict', ((1, 0),), (), 'empty')]
        for label, extra, ids, status in cases:
            selected = {raw: value for raw, value in words.items()
                        if all((value[0] >> i) & 1 == b for i, b in extra)
                        and all(value[1][i] == b for i, b in ids)}
            if label in ('one','zero'):
                assert {v[-1] for v in selected.values()} == {int(label == 'one')}
            params = dict(options, occurrence_pins=base + extra, id_pins=ids)
            result = event_block_solver.solve(*args, **params)
            summaries[backend + '-' + label] = check_result(result, selected, status)
        for cap in ('state_cap','step_cap'):
            limited = event_block_solver.solve(*args, **options, **{cap: 0})
            assert limited['status'] == 'unknown' and limited['reason'] == 'cap'
            assert not limited['samples']
    k5 = event_blocks.decompose(range(5), combinations(range(5), 2))
    assert k5['status'] == 'unknown'
    print(json.dumps(summaries, sort_keys=True))


if __name__ == '__main__':
    main()
