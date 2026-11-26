from itertools import combinations, product


def span(cols):
    values = {0}
    for c in cols:
        values |= {v^c for v in values}
    return values


if __name__ == '__main__':
    tests = 0
    for e in range(1,5):
        for cols in product(range(4),repeat=e):
            whole = span(cols)
            for mask in range(1<<e):
                left = span([c for i,c in enumerate(cols) if mask>>i&1])
                right = span([c for i,c in enumerate(cols) if not mask>>i&1])
                for b in whole:
                    rows = {tuple(int(a^z==b) for z in right) for a in left}
                    rows.discard((0,)*len(right))
                    assert len(rows)*len(whole) == len(left)*len(right)
                    assert all(sum(row)==1 for row in rows)
                    tests += 1
    print(tests,'cut/syndrome cases passed')
