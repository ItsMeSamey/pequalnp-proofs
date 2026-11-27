from itertools import combinations


def check():
    count = 0
    for n in range(1, 5):
        possible = list(combinations(range(n), 2))
        for graph_mask in range(1 << len(possible)):
            edges = [e for j, e in enumerate(possible) if graph_mask >> j & 1]
            alpha = max(s.bit_count() for s in range(1 << n)
                        if all(s & (1 << i | 1 << j) != (1 << i | 1 << j)
                               for i, j in edges))
            for k in range(1, n + 1):
                joined = edges + [(i, n+j) for i in range(n) for j in range(k)]
                baseline = (1 << n) - 1
                scale = (n+k+1)**2
                weights = ([scale+k+1+i for i in range(n)]
                           + [scale+1+j for j in range(k)])
                base_cost = sum(weights[:n])
                affordable = []
                strict = []
                for c in range(1 << (n+k)):
                    if c == baseline or any(not(c & (1<<i | 1<<j)) for i,j in joined):
                        continue
                    if c.bit_count() <= n:
                        affordable.append((c ^ baseline).bit_count())
                    cost = sum(w for i,w in enumerate(weights) if c >> i & 1)
                    assert cost != base_cost
                    if cost < base_cost:
                        strict.append((c ^ baseline).bit_count())
                assert bool(affordable) == bool(strict) == (alpha >= k)
                assert all(d >= 2*k for d in affordable + strict)
                count += 1
    return count


if __name__ == '__main__':
    print(check(), 'graph and threshold pairs passed')
