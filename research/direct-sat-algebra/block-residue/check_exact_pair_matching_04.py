"""04-only bounded checker for the optional installed NetworkX adapter."""
from itertools import product
from pathlib import Path
import sys

LIB = Path("/workspace/scratch/syn_quotients/tools_lib")
sys.path.insert(0, str(LIB))

import networkx as nx
from check_pair_gain_04 import cost_oracle, pair_optimum
from exact_pair_matching import best_exact_partition, exact_pair_partition, exact_pair_witness
from interval_optimizer import minimum_partition


def check(inputs, gates, pins):
    observed = {v for v, bit in pins}
    score = cost_oracle(inputs, gates, observed)
    singles = tuple((i,) for i in range(len(gates)))
    _, ranges = minimum_partition(inputs, gates, observed)
    intervals = tuple(tuple(range(a,b)) for a,b in ranges)
    expected = []
    for seed in (singles, intervals):
        def merged(ids):
            return score(tuple(sorted(i for j in ids for i in seed[j])))
        optimum = pair_optimum(merged, tuple(range(len(seed))))
        value, groups = exact_pair_partition(inputs, gates, observed, seed=seed)
        assert value == optimum == sum(score(group) for group in groups)
        expected.append(value)
    assert best_exact_partition(inputs, gates, observed)[0] == min(expected)
    bad, groups, status, raw = exact_pair_witness(inputs, gates, pins=pins)
    def accepts(bits):
        values = list(bits)
        for a,b in gates:
            values.append(int(not(values[a] and values[b])))
        return all(values[v] == bit for v,bit in pins)
    live = any(accepts(bits) for bits in product((0,1), repeat=inputs))
    assert bad == min(expected) and status == ("sat" if live else "unsat")
    assert (raw is not None and accepts(raw)) if live else raw is None


def main():
    assert Path(nx.__file__).resolve().parent == LIB / "networkx"
    assert nx.__version__ == "3.7"
    check(0, (), ())
    check(2, ((0,1),(0,2)), ((1,1),(3,1)))
    check(2, ((0,1),(0,2)), ((1,1),(1,0)))
    check(4, ((0,1),(2,3),(0,4),(2,5)), ((1,1),(3,1),(6,1),(7,1)))
    check(2, ((0,1),(2,0),(1,2),(3,4),(5,5)), ((6,1),))
    print("five original NAND controls, both exact seed costs and raw SAT/UNSAT checked")


if __name__ == "__main__":
    main()
