"""Check bounded-boundary inference-DAG search against random width-two decompositions."""
from random import Random


def components(vertices, neighbors):
    unseen = set(vertices)
    while unseen:
        start = unseen.pop()
        component = {start}
        stack = [start]
        while stack:
            v = stack.pop()
            new = unseen & neighbors[v]
            unseen -= new
            component |= new
            stack.extend(new)
        yield component


def run(rng, n):
    bags = [{0}]
    tree = [set()]
    parents = [[]]
    neighbors = [set()]
    false = {0}
    for v in range(1, n):
        bag_id = rng.randrange(v) if rng.random() < .3 else v - 1
        old = sorted(bags[bag_id])
        p = rng.sample(old, min(2, len(old)))
        parents.append(p)
        neighbors.append(set(p))
        for x in p:
            neighbors[x].add(v)
        bags.append(set(p) | {v})
        tree.append({bag_id})
        tree[bag_id].add(v)
        if any(x in false for x in p) and rng.random() < .85:
            false.add(v)
    target = max(false)
    W = set(range(n))
    original_bag = {v: v for v in range(n)}

    def centroid(weighted):
        if not weighted:
            return set()
        weight = [0] * n
        for x in weighted:
            weight[original_bag[x]] += 1
        total = sum(weight)
        sub = weight[:]
        par = [min(adj) if i else -1 for i, adj in enumerate(tree)]
        for i in range(n-1, 0, -1):
            sub[par[i]] += sub[i]
        for i, adj in enumerate(tree):
            if 2*(total - sub[i]) <= total and all(2*sub[j] <= total for j in adj if j > i):
                return bags[i]
        raise AssertionError('No centroid')

    stages = 0
    while W:
        stages += 1
        X = set().union(*(neighbors[i] for i in W)) - W
        assert len(X) <= 12 and target in W & false
        assert not any(i in false and i < target for i in X)
        Z = (centroid(W) | centroid(X)) & (W | X)
        parts = list(components(W - Z, neighbors))
        assert all(2*len(part) <= len(W) for part in parts)
        u = min(false & ((Z & W) | {target}))
        if u in Z:
            if not parents[u]:
                assert u == 0
                break
            target = next(v for v in parents[u] if v in false)
        W = next(part for part in parts if target in part)
    assert stages <= n.bit_length() + 1
    return stages


def main():
    rng = Random(962)
    stages = sum(run(rng, rng.randint(5, 100)) for _ in range(300))
    print(f'300 bounded-treewidth proof-flow fixtures, {stages} valid separator states passed.')


if __name__ == '__main__':
    main()
