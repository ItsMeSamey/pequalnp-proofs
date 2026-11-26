"""Check ordinary quartic closures on small negative, even-feasible rooted graphs."""
from random import Random

from check_neutral_signatures import pc


def main():
    rng = Random(613)
    checked = 0
    for trial in range(1500):
        n = rng.randrange(4, 9)
        m = n // 2
        graph = [0] * n
        for i in range(m):
            for j in range(m, n):
                if (i, j) == (0, m) or rng.randrange(2):
                    graph[i] |= 1 << j
                    graph[j] |= 1 << i
        feasible = [x for x in range(1 << n) if x & 1 and x >> m & 1
                    and all(not (x >> i & 1) or not (x & row).bit_count() % 2
                            for i, row in enumerate(graph))]
        if not feasible or any(x.bit_count() % 2 for x in feasible):
            continue
        labels = [4 | int(i == 0) | 2 * int(i == m) for i in range(n)]
        assert pc(graph, labels, 7, 4)
        checked += 1
        if checked == 80:
            break
    assert checked == 80
    print('80 negative odd-total rooted instances admitting an even model passed ordinary degree four.')


if __name__ == '__main__':
    main()
