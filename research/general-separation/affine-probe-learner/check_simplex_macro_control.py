"""Actual raw NAND simplex, original-input witnesses, and an uncollapsed counter."""
from affine_independence_portfolio import counted
from check_binary_fault_solver import raw, simplex
from simplex_macro_control import solve_affine_macros


def main():
    n, circuit = 7, simplex()
    gates, output = circuit
    answer = solve_affine_macros(n, gates, output)
    assert answer is not None and len(answer.equations) == 4
    assert answer.count == 8 and raw(n, circuit, answer.witness) == 1
    for word in range(1 << n):
        satisfies = all(((mask & word).bit_count() & 1) == b for mask, b in answer.equations)
        assert satisfies == bool(raw(n, circuit, word))
    assert solve_affine_macros(2, ((0, 1),), 2) is None
    impossible = solve_affine_macros(1, ((0, 0), (0, 1), (2, 2)), 3)
    assert impossible is not None and (impossible.count, impossible.witness) == (0, None)

    # Keep EVERY NAND in its original order. Two constant-table gates supply
    # the raw format's constant wires, and the final identity selects its output.
    port = {-1: n, -2: n+1, **{i: i for i in range(n)}}
    tables = [(0, 0, 0), (15, 0, 0)]
    for i, (a, b) in enumerate(gates, n):
        port[i] = n + len(tables)
        tables.append((7, port[a], port[b]))
    tables.append((12, port[output], port[output]))
    for budget in (0, 2):
        result = counted(n, tables, max_splits=budget)
        assert result is None or result['count'] == answer.count
        print('uncollapsed max_splits', budget, 'result', result)
    print('ordered NANDs', len(gates), 'equations', answer.equations,
          'count', answer.count, 'original witness', answer.witness)


if __name__ == '__main__':
    main()
