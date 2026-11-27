"""Independent small exhaustive-span and parity checks for direct certificates."""
from functools import reduce
from operator import xor
from itertools import product
from pathlib import Path
import json

from produce_direct import produce, lean_source


def xors(words):
    span = {0}
    for w in words:
        span |= {x ^ w for x in span}
    return span


def verify(raw, trace, expected):
    try:
        c = produce(raw, trace)
    except ValueError:
        assert not expected, (raw, trace)
        return
    assert expected, (raw, trace)
    cols, pins = raw["columns"], raw["forced"]
    t, a, b = raw["names"]
    def inner(row, word):
        return sum((word >> j) & 1 for j in row) % 2
    def word(ids):
        return reduce(xor, (cols[i] for i in ids), 0)
    if c["kind"] == "positive":
        support = set(pins + c["selected"])
        assert support == set(trace["support"]) and set(c["witness"]) <= support
        assert word(c["witness"]) == t
        for row, pair in [(c["rowA"], (1,0)), (c["rowB"], (0,1))]:
            assert all(not inner(row, cols[i]) for i in support)
            assert (inner(row, a), inner(row, b)) == pair
    elif c["kind"] == "outside":
        assert inner(c["row"], t) and not any(inner(c["row"], w) for w in cols)
    else:
        assert c["u"] or c["v"]
        assert set(c["witness"]) <= set(pins)
        assert word(c["witness"]) == (a*c["u"] ^ b*c["v"] ^ t*c["y"])


def run():
    tested = 0
    for n in range(4):
        for columns in product(range(8), repeat=n):
            for p in range(1 << n):
                pins = [i for i in range(n) if p >> i & 1]
                raw = {"columns": list(columns), "names":[1,2,4], "forced":pins}
                whole = xors(columns)
                forced = xors(columns[i] for i in pins)
                verify(raw, {"terminal":"outside"}, 1 not in whole)
                verify(raw, {"terminal":"pins_conflict"}, bool(forced - {0,1}))
                tested += 2
                for mask in range(1 << n):
                    support = [i for i in range(n) if mask >> i & 1]
                    expected = (mask & p) == p and xors(columns[i] for i in support) == {0,1}
                    verify(raw, {"terminal":"single","support":support}, expected)
                    tested += 1
    print(f"{tested} independent tiny-physical certificate checks passed")
    fixtures = {"positive":{"terminal":"excluded","support":[0,2,3]},
                "conflict":{"terminal":"pins_conflict"}, "outside":{"terminal":"outside"}}
    chunks = ["import ThreeNameGenericDirect\n"]
    for kind,trace in fixtures.items():
        raw = json.loads((Path(__file__).parent/"samples"/(kind+".json")).read_text())
        source = lean_source(raw, trace)
        assert "sorry" not in source
        assert produce(raw,trace)["kind"] == kind
        chunks.append(source.removeprefix("import ThreeNameGenericDirect\n"))
    archived = Path(__file__).parent / "lean" / "ThreeNameEmittedSamples.lean"
    assert archived.read_text() == "\n".join(chunks)
    print("all three emitted Lean instances reproduced byte-for-byte")


if __name__ == "__main__":
    run()
