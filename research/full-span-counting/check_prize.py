"""Exhaustively audit profile-level primal-dual cover on small random set systems."""
from itertools import combinations
from random import Random


def check(groups, cost, penalty):
    n = len(penalty)
    picked = set()
    ignored = set()
    y = [0]*n
    def covered(p):
        return any(p in groups[i] for i in picked)
    while True:
        p = next((p for p in range(n) if p not in ignored and not covered(p)), None)
        if p is None:
            break
        inc = [i for i,g in enumerate(groups) if p in g]
        slack = lambda i: cost[i]-sum(y[v] for v in groups[i])
        delta = min([penalty[p]-y[p]]+[slack(i) for i in inc])
        assert delta >= 0
        y[p] += delta
        tight = next((i for i in inc if slack(i)==0), None)
        if tight is None:
            assert y[p] == penalty[p]
            ignored.add(p)
        else:
            picked.add(tight)
    opt = min(sum(cost[i] for i in chosen)+
              sum(penalty[p] for p in range(n) if all(p not in groups[i] for i in chosen))
              for k in range(len(groups)+1) for chosen in combinations(range(len(groups)),k))
    f = max([1]+[sum(p in g for g in groups) for p in range(n)])
    actual = sum(cost[i] for i in picked)
    remaining = sum(penalty[p] for p in range(n) if not covered(p))
    assert actual+f*remaining <= f*sum(y) <= f*opt
    assert sum(penalty[p] for p in ignored) <= sum(y)


def main():
    rng = Random(8529)
    for _ in range(500):
        n = rng.randrange(10)
        groups = [{p for p in range(n) if rng.randrange(4)==0} for _ in range(rng.randrange(8))]
        check(groups,[rng.randrange(10) for g in groups],[rng.randrange(10) for p in range(n)])
    print("500 prize-cover instances passed f-LMP and cumulative penalty checks.")


if __name__=='__main__':
    main()
