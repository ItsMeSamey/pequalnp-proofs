from itertools import combinations_with_replacement
from random import Random
from routing import route


def labels(n, gates, feedback, setting):
    successor = list(range(n))
    for i, (a, b, c) in enumerate(gates):
        if setting >> i & 1:
            rotate = {a:b, b:c, c:a}
            successor = [rotate.get(v, v) for v in successor]
    # Follow the feedback starting immediately before the feedback layer.
    step = [successor[feedback[v]] for v in range(n)]
    orbit = [-1]*n
    for v in range(n):
        u = v
        while orbit[u] < 0:
            orbit[u] = v
            u = step[u]
    return orbit


def check():
    rng = Random(20261126)
    total = yes = settings = 0
    for case in range(200):
        n = rng.randrange(3, 8)
        gates = [rng.sample(range(n), 3) for _ in range(case % 7)]
        feedback = rng.sample(range(n), n)
        oracle = [labels(n, gates, feedback, s) for s in range(1 << len(gates))]
        settings += len(oracle)
        order = rng.sample(range(len(gates)), len(gates))
        for a, b in combinations_with_replacement(range(n), 2):
            choice = route(n, gates, feedback, (a,b), order)
            truth = any(row[a] == row[b] for row in oracle)
            if (choice is not None) != truth or (truth and oracle[choice][a] != oracle[choice][b]):
                raise AssertionError((case,a,b,choice))
            total += 1
            yes += truth
    print(f"200 networks, {settings} settings, {total} root pairs, {yes} witnesses, {total-yes} negatives")


if __name__ == "__main__":
    check()
