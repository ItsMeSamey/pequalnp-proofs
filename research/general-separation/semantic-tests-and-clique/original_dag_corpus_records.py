"""Emit all original circuits, oracle counts and the independent rule results as JSONL."""
import json
from random import Random
from affine_independence_portfolio import counted
from affine_weight_portfolio import affine_weight_count
from original_dag_portfolio import analyze, compact, corpus, normalize, table, weight_control
from quadratic_frontier_portfolio import coupled_quadratics, quadratic_frontier_count


def circuits():
    yield from corpus()
    control = weight_control()
    yield 'all-triples', control['q'], control['gates']
    rng = Random(48103)
    for index in range(96):
        gates = []
        q = 4
        for j in range(5 + index % 5):
            gates.append((rng.choice((8, 6, 14, 7, 9, 11)), rng.randrange(q+j), rng.randrange(q+j)))
        yield f'random-{index}', q, gates
    for q in (4, 8, 12):
        yield f'coupled-quadratics-{q}', q, coupled_quadratics(q)


def record(name, q, gates):
    truth = table(q, gates)
    g = compact(q, gates)
    row = dict(name=name, q=q, gates=gates, live_gates=len(g), oracle_table=hex(truth),
               oracle_ones=truth.bit_count(), affine_weight=affine_weight_count(q, gates),
               quadratic_cut=quadratic_frontier_count(q, gates))
    row['independence'] = [counted(q, gates, depth) for depth in (0, 1, 2)]
    for result in [row['affine_weight'], row['quadratic_cut'], *row['independence']]:
        assert result is None or result['count'] == row['oracle_ones']
    products = len(normalize(q, g)[0]) // 2
    if q <= 8 and q+products <= 15 and len(gates) <= 160:
        row['original_portfolio'] = analyze(q, gates)
    else:
        row['original_portfolio'] = dict(skipped=True, inputs=q, products=products,
            input_cap=8, precheck_dimension_cap=15, original_gate_cap=160)
    return row


if __name__ == '__main__':
    for original in circuits():
        print(json.dumps(record(*original), separators=(',', ':'), sort_keys=True))
