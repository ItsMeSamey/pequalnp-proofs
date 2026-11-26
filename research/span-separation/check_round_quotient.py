"""Exhaust the small equal-quotient lifts and their four-dimensional interfaces."""
from itertools import combinations

NO = (20, 33, 53, 67, 91, 98, 120, 140, 145, 175, 176, 197)
YES = (28, *NO[1:])


def span(vectors):
    values = {0}
    for v in vectors:
        values |= {x ^ v for x in values}
    return values


def catalog(columns):
    return {frozenset(v for v in span(subset) if v < 16)
            for size in range(len(columns) + 1)
            for subset in combinations(columns, size)}


if __name__ == "__main__":
    all_spaces = {frozenset(span(subset)) for n in range(5)
                  for subset in combinations(range(1, 16), n)}
    assert len(all_spaces) == 67
    assert catalog(NO) == {h for h in all_spaces if 1 not in h or max(h) >= 8}
    assert catalog(YES) == all_spaces
    assert catalog(NO + (215, 226)) == catalog(NO)
    assert catalog(YES + (215, 226)) == all_spaces
    for columns in (NO, YES):
        assert tuple(v >> 4 for v in columns) == tuple(range(1, 13))
        assert len(span(columns)) == 256
        assert span([33, 67]) == {0, 33, 67, 98}
    print("Round 12-point quotient: 62 NO and 67 YES traces, both ranks 8 before projection")
