"""Exhaustive binary common-basis criterion check in ambient dimension three."""
from itertools import combinations


def span(columns):
    values = {0}
    for col in columns:
        values |= {x ^ col for x in values}
    return values


def subsets(seq):
    return (x for size in range(len(seq) + 1) for x in combinations(seq, size))


def check():
    count = 0
    for ground in subsets(range(1, 8)):
        candidates = [(x, span(x)) for x in subsets(ground)]
        for u in range(1, 8):
            for w in range(1, 8):
                if u == w:
                    continue
                dimension = len(span((*ground, u, w))).bit_length() - 1
                witness = any(u in space and w not in space for _, space in candidates)
                criterion = any(
                    len(x) == dimension - 1 and len(space) == 2 ** len(x)
                    and w not in space and (u ^ w) not in space
                    for x, space in candidates
                )
                assert criterion == witness, (ground, u, w, dimension)
                count += 1
    print(f"Agreement on {count} labeled instances.")


if __name__ == "__main__":
    check()
