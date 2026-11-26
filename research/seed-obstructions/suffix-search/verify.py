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
    @functools.lru_cache(100000)
    def possible(state, spare):
        if len(state) == 1:
            return separates(state[0]) == full
        covers = list(map(separates, state))
        for i, j in itertools.combinations(range(len(state)), 2):
            rest = tuple(v for k, v in enumerate(state) if k not in (i,j))
            covered = 0
            for k, c in enumerate(covers):
                if k not in (i,j):
                    covered |= c
            for v in (state[i] & state[j], state[i] | state[j]):
                base = covered | separates(v)
                for n in range(min(2, spare)+1):
                    for keep in itertools.combinations((i,j), n):
                        coverage = base
                        for k in keep:
                            coverage |= covers[k]
                        if coverage == full:
                            new = rest + (v,) + tuple(state[k] for k in keep)
                            if possible(tuple(sorted(new)), spare-n):
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
    instances = [tuple(map(int, sys.argv[1:]))] if len(sys.argv)>1 else [(18968,17),(21968,16)]
    for seed, prefix in instances:
        verify(seed, prefix)
