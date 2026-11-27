from itertools import combinations, product
from random import Random
from pins import solve

def words(n):
    def fill(w, i):
        if i == n:
            yield tuple(w)
            return
        p = w.index(None)
        for j in range(p+1, len(w)):
            if w[j] is None:
                w[p] = w[j] = i
                yield from fill(w, i+1)
                w[p] = w[j] = None
    yield from fill([None]*(2*n), 0)

def models(w, marks):
    n = len(marks)
    edges = set()
    for a,b in combinations(range(n), 2):
        restricted = [v for v in w if v in (a,b)]
        if restricted[0] == restricted[2]:
            edges.add((a,b))
    witnesses = []
    for mask in range(1 << n):
        chosen = {i for i in range(n) if mask & (1<<i)}
        if all(sum(tuple(sorted((v,u))) in edges for u in chosen) % 2 == marks[v] for v in chosen):
            witnesses.append(chosen)
    return witnesses

def check(w, marks, pins, witnesses, labels=None, target=0):
    labels = labels if labels is not None else [0]*len(marks)
    def ok(S):
        mask = 0
        for i in S:
            mask ^= labels[i]
        return mask == target and all((i in S) == b for i,b in pins.items())
    got = solve(w, marks, pins, labels, target)
    assert (got is not None) == any(ok(S) for S in witnesses)
    assert got is None or got in witnesses and ok(got)

if __name__ == '__main__':
    total = 0
    for n in (1,2,3):
        for w in words(n):
            for marks in product(range(2), repeat=n):
                witness = models(w, marks)
                for signs in product((0,1), repeat=n):
                    check(w, marks, dict(enumerate(signs)), witness)
                    total += 1
    rng = Random(1834)
    for _ in range(160):
        n = rng.randrange(3,8)
        w = list(range(n))*2
        rng.shuffle(w)
        marks = [rng.randrange(2) for _ in range(n)]
        witness = models(w, marks)
        check(w, marks, dict.fromkeys(rng.sample(range(n),3),1), witness)
        labels=[0]*n
        for i in rng.sample(range(n),3):
            labels[i] = rng.randrange(8)
        check(w, marks, {}, witness, labels, rng.randrange(8))
        total += 2
    print(f'{total} deterministic matching decisions and witnesses checked by graph enumeration.')
