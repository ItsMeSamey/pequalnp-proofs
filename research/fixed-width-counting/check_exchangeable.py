from itertools import combinations, product
from random import Random

rng = Random(703)
for case in range(400):
    n = rng.randint(1, 8)
    chosen = [rng.randint(0, 3) for _ in range(n)]
    groups = [[i for i in range(n) if chosen[i] == color] for color in set(chosen)]
    params = []
    for g in groups:
        p = rng.randint(0,len(g))
        q = rng.randint(0,len(g)-p)
        params.append((p,q))
    choices = []
    for g,(p,q) in zip(groups,params):
        choices.append([(set(a),set(b)) for a in combinations(g,p)
                        for b in combinations(set(g)-set(a),q)])
    orbit = [(set.union(*(a for a,_ in v)), set.union(*(b for _,b in v)))
             for v in product(*choices)]
    for v in range(1<<n):
        ones = {i for i in range(n) if v>>i&1}
        truth = all(bool(a&ones) or bool(b-ones) for a,b in orbit)
        by_weight = any(len(ones.intersection(g))<q or len(ones.intersection(g))>len(g)-p
                        for g,(p,q) in zip(groups,params))
        assert truth == by_weight
print("400 orbit families checked at every Boolean assignment")
