"""Actual ordered-image checks for exhaustive source and phase-residual paths."""
from read_two_ring_nonzero import compile_nonzero
from ring_image_guard_search import decide


def physical(a, rows):
    raw = compile_nonzero(a, rows)
    return tuple(raw[key] for key in ("n", "clauses", "point", "k"))


def main():
    # Seven declared source variables; only x_4 occurs. Negative unit syntax
    # makes the positive-demand matching backend inapplicable.
    data = physical(7, [(-4,)])
    refused = decide(*data, max_assignments=1)
    assert (refused["status"], refused["required_log2"], refused["tested"]) == ("unknown", 1, 0)
    sat = decide(*data, max_assignments=2)
    assert sat["search"] == "source" and sat["assignment"][3] == 0
    unsat = decide(*physical(1, [(1,), (-1,)]), max_assignments=None)
    assert (unsat["status"], unsat["tested"]) == ("zero", 2)
    assert decide(0, (), (), 1)["status"] == "off_image"

    # Five C4 roots. Each adjacent pair of named edges conflicts, and its
    # positive star must be hit. Each cycle independently chooses an alternation.
    rows = []
    for start in range(1, 21, 4):
        for j in range(4):
            a, b = start+j, start+(j+1)%4
            rows.extend([(-a, -b), (a, b)])
    chosen = tuple(range(1, 21, 4))
    rows.append(chosen)
    data = physical(20, rows)
    refused = decide(*data, max_assignments=31)
    assert (refused["search"], refused["required_log2"]) == ("residual", 5)
    sat = decide(*data, max_assignments=32)
    assert sat["status"] == "nonzero" and sat["search"] == "residual"
    assert all(any(sat["assignment"][abs(x)-1] == (x > 0) for x in row) for row in rows)
    print("source and five-cycle residual caps, physical witnesses, UNSAT and off-image passed")


if __name__ == "__main__":
    main()
