"""Compare vertex-cut certificates for random clique fills and connected surrogates."""
import itertools
import random

rng = random.Random(7307)
total = 0
for trial in range(360):
    n = rng.randrange(4,10)
    bags = [rng.sample(range(n),rng.randrange(2,min(n,5)+1)) for _ in range(rng.randrange(1,n+3))]
    true = {tuple(sorted(e)) for e in itertools.combinations(range(n),2) if rng.random()<0.12}
    torso = set(true)
    small = set(true)
    for bag in bags:
        torso.update(tuple(sorted(e)) for e in itertools.combinations(bag,2))
        small.update(tuple(sorted((v,rng.choice(bag[:i])))) for i,v in enumerate(bag) if i)
    degree = max(sum(v in b for b in bags) for v in range(n))
    a = max(map(len,bags))
    def components(edges, removed):
        groups=[{v} for v in range(n) if v not in removed]
        for u,v in edges:
            if u in removed or v in removed:
                continue
            i=next(i for i,c in enumerate(groups) if u in c)
            j=next(i for i,c in enumerate(groups) if v in c)
            if i!=j:
                group=groups[j]
                groups[i].update(group)
                groups.remove(group)
        return groups
    def cuts(graph):
        for z in range(n-1):
            for cut in itertools.combinations(range(n),z):
                if len(components(graph,cut))>1:
                    return z
        return n-1
    assert cuts(small)*(1+degree*a*(a-1)//2)>=cuts(torso)
    for z in range(n-1):
        removed=set(rng.sample(range(n),z))
        groups=components(small,removed)
        across={e for e in torso if not removed.intersection(e) and not any(set(e)<=g for g in groups)}
        hits=[set(b) for b in bags if removed.intersection(b)]
        assert all(any(set(e)<=b for b in hits) for e in across)
        assert len(across)<=degree*z*a*(a-1)//2
        total+=1
print(f"360 surrogate connectivity comparisons, {total} separating-edge checks")
