"""Differential audit of compressed child joins for induced even vertex sets."""
from functools import reduce
from itertools import combinations, product
from operator import xor
from random import Random


def xsum(values):
    return reduce(xor, values, 0)


def bucket_join(states, t):
    # Each state is the label table for this child's actual shared-parent bit.
    n = len(states)
    out = {0}
    width = max(0, (n - 1).bit_length())
    for k in range(1, min(t, n) + 1):
        for coordinates in combinations(range(width), min(width, k - 1)):
            buckets = {}
            for j, labels in enumerate(states):
                key = tuple((j >> b) & 1 for b in coordinates)
                buckets.setdefault(key, []).append(labels)
            for selected in combinations(buckets.values(), k):
                for goals in product(range(1, 1 << t), repeat=k):
                    feasible = True
                    for group, goal in zip(selected, goals):
                        # Exhaust all independent selector bits in this bucket.
                        eligible = sum((goal in labels) << j for j, labels in enumerate(group))
                        if not any((eligible & w).bit_count() % 2
                                   for w in range(1 << len(group))):
                            feasible = False
                            break
                    if feasible:
                        out.add(xsum(goals))
    return out


def run_case(specs, labels, t):
    # A block record is (vertices, undirected edges, parent index, articulation).
    trees = []
    for i in reversed(range(len(specs))):
        verts, edges, parent, art = specs[i]
        children = [tree for tree in trees if specs[tree[0]][2] == i]
        table = [set(), set()]
        allv = set(verts)
        alle = list(edges)
        for _, childv, childe, _ in children:
            allv.update(childv)
            alle.extend(childe)
        for mask in range(1 << len(verts)):
            selected = {v for j, v in enumerate(verts) if (mask >> j) & 1}
            if any(sum((u == v and w in selected) or (w == v and u in selected)
                       for u, w in edges) % 2 for v in selected):
                continue
            states = [tabs[int(specs[j][3] in selected)] for j, _, _, tabs in children]
            assert all(0 in options for options in states)
            joined = bucket_join(states, t)
            exact = {xsum(vals) for vals in product(*states)}
            assert joined == exact
            weight = xsum(labels[v] for v in selected if v != art)
            table[int(art in selected)].update(weight ^ g for g in joined)

        # Independent whole-subtree oracle: parity of induced degrees via bit masks.
        vs = sorted(allv)
        adj = [0] * len(vs)
        for u, v in alle:
            a, b = vs.index(u), vs.index(v)
            adj[a] |= 1 << b
            adj[b] |= 1 << a
        oracle = [set(), set()]
        for mask in range(1 << len(vs)):
            taken = [j for j in range(len(vs)) if (mask >> j) & 1]
            if all((mask & adj[j]).bit_count() % 2 == 0 for j in taken):
                state = int(art in allv and vs.index(art) in taken)
                oracle[state].add(xsum(labels[vs[j]] for j in taken if vs[j] != art))
        assert table == oracle, (specs, labels, i, table, oracle)
        trees.append((i, allv, alle, table))
    return len(trees)


def generate(rng, count, shared=False):
    nxt = 0
    specs = []
    for i in range(count):
        parent = (0 if shared else rng.randrange(i)) if i else -1
        art = (0 if shared else rng.choice(specs[parent][0])) if i else None
        size = rng.choice([2, 2, 3, 4]) if not shared else 2
        vs = ([art] if i else []) + list(range(nxt, nxt + size - bool(i)))
        nxt += size - bool(i)
        edges = list(zip(vs, vs[1:]))
        if size > 2:
            edges.append((vs[-1], vs[0]))
        if size == 4 and rng.randrange(2):
            edges.append((vs[0], vs[2]))
        specs.append((vs, edges, parent, art))
    return specs, nxt


if __name__ == '__main__':
    rng = Random(921869)
    checks = 0
    for trial in range(160):
        t = trial % 4
        specs, n = generate(rng, rng.randint(1, 5), trial % 5 == 0)
        checks += run_case(specs, [rng.randrange(1 << t) for _ in range(n)], t)
    # Six siblings at one separator. Distinct children needed for the XOR 7.
    specs, n = generate(rng, 7, True)
    checks += run_case(specs, [0, 0, 1, 2, 4, 0, 0, 0], 3)
    print(f'161 block trees, {checks} block/subtree tables, all passed')

    # Check algebraic hitting of every simultaneous nonempty support in three
    # disjoint two-child buckets. x^5+x^2+1 is irreducible over GF(2).
    def mul(a, b):
        c = 0
        while b:
            if b & 1:
                c ^= a
            b >>= 1
            a <<= 1
            if a & 32:
                a ^= 37
        return c

    id_powers = []
    for alpha in range(32):
        row = [1]
        for j in range(5):
            row.append(mul(row[-1], alpha))
        id_powers.append(row)
    for supports in product((1, 2, 3), repeat=3):
        assert any(all(xsum(powers[2*i + j] for j in range(2) if (s >> j) & 1)
                       for i, s in enumerate(supports)) for powers in id_powers)
    print('27 simultaneous three-bucket selector supports passed')
