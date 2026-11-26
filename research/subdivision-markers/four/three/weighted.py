"""Three-port weighted gluing versus direct induced-subset enumeration."""
from dataclasses import dataclass, field
from itertools import combinations, permutations, product
from random import Random

PAIRS = (3, 5, 6)
REPS = (
    ((0, 3), (1, 3), (2, 3)),
    ((0, 3), (1, 3), (2, 4), (3, 4)),
    ((0, 3), (0, 4), (1, 3), (2, 4), (3, 4)),
    ((0, 3), (1, 3), (0, 4), (2, 4), (1, 5), (2, 5)),
)


def maskof(vs):
    return sum(1 << v for v in vs)


def project(mask, ports):
    return sum(((mask >> v) & 1) << j for j, v in enumerate(ports))


def odds(selected, edges):
    result = 0
    for a, b in edges:
        pair = (1 << a) | (1 << b)
        if selected & pair == pair:
            result ^= pair
    return result


def label(mask, weights):
    value = 0
    for v, w in enumerate(weights):
        if (mask >> v) & 1:
            value ^= w
    return value


def oracle(vs, edges, ports, weights):
    pm = maskof(ports)
    support = maskof(vs)
    s = support
    tab = {}
    while True:
        odd = odds(s, edges)
        if not odd & ~pm:
            tab.setdefault((project(s, ports), project(odd, ports)), set()).add(
                label(s & ~pm, weights))
        if not s:
            return tab
        s = (s - 1) & support


def gadget(P, Q):
    if P != set(PAIRS):
        edges = []
        for v, pair in enumerate(sorted(P), 3):
            edges.extend((j, v) for j in range(3) if (pair >> j) & 1)
        return edges
    prefix = PAIRS[:len(Q)]
    for perm in permutations(range(3)):
        if {maskof(perm[j] for j in range(3) if (x >> j) & 1) for x in prefix} == Q:
            transform = lambda j: perm[j] if j < 3 else j
            return [(transform(a), transform(b)) for a, b in REPS[len(Q)]]
    raise AssertionError(Q)


@dataclass
class Region:
    ports: tuple
    bag: tuple
    own: set = field(default_factory=set)
    children: list = field(default_factory=list)


def child_index(ports, vs, edges, tab):
    owned = {e for e in edges if set(e) <= set(ports)}
    shifted = {(b, q ^ project(odds(maskof(v for j, v in enumerate(ports)
                     if (b >> j) & 1), owned), ports)): vals for (b, q), vals in tab.items()}
    P = {p for p in PAIRS if (p, p) in shifted}
    Q = {p for p in PAIRS if (7, p) in shifted}
    gadget_edges = gadget(P, Q)
    size = max((v for e in gadget_edges for v in e), default=2) - 2
    alternatives = {}
    for b in range(8):
        choices = set()
        for aux in range(1 << size):
            q = odds(b | (aux << 3), gadget_edges)
            if q & ~7:
                continue
            canonical = min(shifted[b, q])
            corrections = tuple(sorted(canonical ^ w for w in shifted[b, q]))
            assert 0 in corrections
            choices.add((maskof(v for j, v in enumerate(ports) if (q >> j) & 1),
                         canonical, corrections))
        alternatives[b] = choices
    return owned, alternatives


def verify(region, weights, t, counts):
    vs = set(region.bag)
    edges = region.own.copy()
    skeleton = region.own.copy()
    children = []
    for child in region.children:
        cv, ce, ct = verify(child, weights, t, counts)
        assert vs & cv == set(child.ports) and edges.isdisjoint(ce)
        own, alternatives = child_index(child.ports, cv, ce, ct)
        skeleton.update(own)
        vs.update(cv)
        edges.update(ce)
        children.append((child.ports, alternatives))

    computed = {}
    pm = maskof(region.ports)
    for m in range(1 << len(region.bag)):
        sel = maskof(v for j, v in enumerate(region.bag) if (m >> j) & 1)
        for contributions in product(*(choices[project(sel, pts)] for pts, choices in children)):
            odd = odds(sel, skeleton)
            base = label(sel & ~pm, weights)
            sparse = {(0, 0)}
            for flip, canonical, corrections in contributions:
                odd ^= flip
                base ^= canonical
                sparse = {(s ^ d, k + bool(d)) for s, k in sparse for d in corrections
                          if k + bool(d) <= t}
            # Test each outward row via an extra two-edge path. To test q=0
            # no path is added; for q a pair require the proxy and both ends.
            # This compensates exactly that pair's odd degree at the ports.
            for q in (0,) + PAIRS:
                pts = [v for j, v in enumerate(region.ports) if (q >> j) & 1]
                if q:
                    vm = max(vs) + 1
                    if sel & maskof(pts) != maskof(pts):
                        continue
                    path_odd = odds(sel | (1 << vm), [(v, vm) for v in pts])
                else:
                    path_odd = 0
                if not odd ^ path_odd:
                    computed.setdefault((project(sel, region.ports), q), set()).update(
                        base ^ s for s, _ in sparse)
    direct = oracle(vs, edges, region.ports, weights)
    assert computed == direct, (region, weights, computed, direct)
    counts[0] += 1
    return vs, edges, computed


def generate(rng, many=False):
    root = Region((0, 1, 2), (0, 1, 2, 3, 4))
    nodes = [root]
    n = 5
    for i in range(rng.randint(1, 4)):
        parent = root if many else rng.choice(nodes)
        if many:
            pts = ((0,1,2), (2,1,0), (0,2,3), (0,3,4))[i]
        else:
            pts = tuple(rng.sample(parent.bag, 3))
        new = tuple(range(n, n + rng.randrange(3)))
        n += len(new)
        sub = Region(pts, pts + new)
        parent.children.append(sub)
        nodes.append(sub)
    owners = {}
    for node in nodes:
        for a,b in combinations(node.bag, 2):
            owners.setdefault(tuple(sorted((a,b))), []).append(node)
    for pair, allowed in owners.items():
        if rng.random() < .55:
            rng.choice(allowed).own.add(pair)
    return root, n


if __name__ == '__main__':
    rng = Random(20262411)
    counts = [0]
    for i in range(400):
        tree, n = generate(rng, i % 2 == 0)
        t = i % 4
        verify(tree, [rng.randrange(1 << t) for _ in range(n)], t, counts)
    # Force every complete-P signature under each permutation of the three ports,
    # each with a second child sharing two ports; vary ownership of direct edges.
    for j, rep in enumerate(REPS):
        for perm in permutations(range(3)):
            for owned in range(4):
                root = Region((0,1,2), (0,1,2,3))
                convert = lambda k: perm[k] if k < 3 else k + 1
                es = {tuple(sorted((convert(a), convert(b)))) for a,b in rep}
                bag = (0,1,2) + tuple(sorted({v for e in es for v in e if v > 3}))
                a = Region((0,1,2), bag, es)
                b = Region((1,0,3), (1,0,3,7), {(0,7),(1,7),(3,7)})
                root.children.extend((a,b))
                if owned:
                    (root,a,b)[owned-1].own.add((0,1))
                verify(root, [0,1,2,3,1,0,3,2], 2, counts)
    print(f'496 trees, {counts[0]} weighted subtree tables passed')
