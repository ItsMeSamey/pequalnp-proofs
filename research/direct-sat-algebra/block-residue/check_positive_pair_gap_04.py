"""04 fixture for ordinary positive-output SAT and UNSAT interval/pair gaps."""
from itertools import product

from interval_optimizer import minimum_partition
from pair_optimizer import greedy_pair_partition, pair_interval_witness


def circuit(k, polarity):
    gates = []
    n = k + 1

    def nand(x, y):
        wire = n + len(gates)
        gates.append((x, y))
        return wire

    zs = [nand(0, i) for i in range(1, k + 1)]
    ws = [nand(0, z) for z in zs]
    s = nand(ws[0], ws[1])
    for w in ws[2:]:
        s = nand(s, w)
    u = nand(0, 0)
    v = s if polarity else nand(s, s)
    h = nand(u, v)
    return gates, nand(h, h)


def replay(raw, gates, output):
    values = list(raw)
    for x, y in gates:
        values.append(int(not (values[x] and values[y])))
    return values[output]


def main():
    for k, polarity in product((3, 4), (0, 1)):
        n = k + 1
        gates, output = circuit(k, polarity)
        models = {raw for raw in product((0, 1), repeat=n) if replay(raw, gates, output)}
        assert len(models) == (2**k if polarity == k % 2 else 0)
        interval, _ = minimum_partition(n, gates, (output,))
        pair, _ = greedy_pair_partition(n, gates, (output,))
        assert interval >= 2*k-1 and pair <= k
        score, _, raw = pair_interval_witness(n, gates, pins=[(output, 1)])
        assert score <= pair and (raw is None) == (not models)
        if raw is not None:
            assert tuple(raw) in models
    print("single positive-output interval/pair gaps verified")


if __name__ == "__main__":
    main()
