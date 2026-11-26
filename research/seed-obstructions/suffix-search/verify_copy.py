import functools
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

source = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(source))
from verify_packing import samples
raw, front, target = samples(source / 'L-meta-18968.json')
rows = [r & ((1 << 38) - 1) for r in raw]
positives = sorted({r for k, r in enumerate(rows) if (target ^ front) >> k & 1})
negatives = {r for k, r in enumerate(rows) if not target >> k & 1}
maximal = sorted(r for r in negatives if not any(r != t and not r & ~t for t in negatives))
assert len(positives) == 28 and len(maximal) == 245

def indices(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask ^= low

def verify(seed, prefix):
    recipes = json.loads(Path(__file__).with_name('recipes.json').read_text())[str(seed)]
    def evaluate(row):
        for i, (op, a, b) in enumerate(recipes[:prefix], 38):
            x, y = row >> a, row >> b
            row |= ((x & y if op == 'and' else x | y) & 1) << i
        return row
    pos, neg = list(map(evaluate, positives)), list(map(evaluate, maximal))
    size = 38 + prefix
    capacity = 34 - prefix
    cuts = []
    for mask in sorted({p & ~n for p in pos for n in neg}, key=int.bit_count):
        if not any(c & mask == c for c in cuts):
            cuts.append(mask)
    def supports(selected, available, slots):
        uncovered = [c & available for c in cuts if not c & selected]
        if not uncovered:
            for k in range(slots + 1):
                for tail in itertools.combinations(indices(available), k):
                    yield selected | sum(1 << i for i in tail)
            return
        if slots:
            choices = min(uncovered, key=int.bit_count)
            for i in indices(choices):
                bit = 1 << i
                available ^= bit
                yield from supports(selected | bit, available, slots - 1)
    columns = [sum(((r >> i) & 1) << k for k, r in enumerate(pos+neg)) for i in range(size)]
    full = (1 << (len(pos)*len(neg))) - 1
    @functools.lru_cache(None)
    def separates(column):
        positive = column & ((1 << len(pos)) - 1)
        negative = ((1 << len(neg)) - 1) ^ (column >> len(pos))
        return sum(negative << (i * len(neg)) for i in indices(positive))
    negative_mask = (1 << len(neg)) - 1

    @functools.lru_cache(200000)
    def project(pairs):
        positive = negative = 0
        for i in range(len(pos)):
            row = pairs & negative_mask
            if row:
                positive |= 1 << i
                negative |= row
            pairs >>= len(neg)
        return positive, negative

    def private_rows(state):
        coverage = list(map(separates, state))
        following = [0] * (len(coverage)+1)
        for i in reversed(range(len(coverage))):
            following[i] = following[i+1] | coverage[i]
        preceding = 0
        result = []
        for i, c in enumerate(coverage):
            private = c & ~(preceding | following[i+1])
            result.append(project(private))
            preceding |= c
        return result

    def incompatible(private, spare):
        if spare > 1:
            return False
        n = len(private)
        edges = [[0]*n for _ in range(2)]
        for i, j in itertools.combinations(range(n), 2):
            for side in (0, 1):
                if private[i][side] & private[j][side]:
                    edges[side][i] |= 1 << j
                    edges[side][j] |= 1 << i
        if spare == 1:
            colors = {}
            for i in range(n):
                if i in colors:
                    continue
                colors[i] = 0
                stack = [i]
                while stack:
                    k = stack.pop()
                    for j in indices(edges[0][k] & edges[1][k]):
                        if j in colors:
                            if colors[j] == colors[k]:
                                return True
                        else:
                            colors[j] = 1 - colors[k]
                            stack.append(j)
            return False

        def compatible(group):
            if group.bit_count() < 2:
                return True
            for graph in edges:
                frontier = group & -group
                component = 0
                while frontier:
                    component |= frontier
                    neighbors = 0
                    for k in indices(frontier):
                        neighbors |= graph[k]
                    frontier = neighbors & group & ~component
                if component != group:
                    return compatible(component) and compatible(group ^ component)
            return False
        return not compatible((1 << n)-1)

    @functools.lru_cache(300000)
    def possible(state, spare, marked=()):
        if len(state) == 1:
            return separates(state[0]) == full
        private = private_rows(state)
        if incompatible(private, spare):
            return False
        if spare and len(marked) <= 1:
            for x in marked or set(state):
                if possible(tuple(sorted(state+(x,))), spare-1):
                    return True
        for i, j in itertools.combinations(range(len(state)), 2):
            u, v = state[i], state[j]
            positive_i, negative_i = private[i]
            positive_j, negative_j = private[j]
            candidates = []
            if not (positive_i & ~v or positive_j & ~u):
                candidates.append(u & v)
            if not (negative_i & (v >> len(pos)) or negative_j & (u >> len(pos))):
                candidates.append(u | v)
            if not candidates:
                continue
            rest = tuple(x for k, x in enumerate(state) if k not in (i,j))
            for x in candidates:
                new = tuple(sorted(rest + (x,)))
                if not spare:
                    if possible(new, 0):
                        return True
                    continue
                # Interchangeable equal columns can represent marked and unmarked wires.
                for a, b in itertools.product((0, 1), repeat=2):
                    saved = list(marked)
                    unmarked = list(state)
                    for m in marked:
                        unmarked.remove(m)
                    try:
                        (saved if a else unmarked).remove(u)
                        (saved if b else unmarked).remove(v)
                    except ValueError:
                        continue
                    saved.append(x)
                    if possible(new, spare, tuple(sorted(saved))):
                        return True
        return False
    counts = Counter()
    for support in supports(0, (1 << size)-1, capacity):
        cardinality = support.bit_count()
        counts[cardinality] += 1
        state = tuple(sorted(columns[i] for i in indices(support)))
        if possible(state, capacity-cardinality):
            raise RuntimeError(f'Completion found for {seed} prefix {prefix}, support {support}')
    print(f'{seed} prefix {prefix} impossible; supports by size {dict(sorted(counts.items()))}', flush=True)

if __name__ == '__main__':
    instances = [tuple(map(int, sys.argv[1:]))] if len(sys.argv)>1 else [(18968,15),(21968,15)]
    for seed, prefix in instances:
        verify(seed, prefix)
