from model import fit, eligible, ROOT
from itertools import permutations, product, combinations
from collections import Counter
import json, sys

def transforms(dep, p):
    k = len(dep)
    d = k - p
    for od in permutations(range(d)):
        for ot in permutations(range(d, k)):
            order = od + ot
            for flip in product(range(2), repeat=k):
                mapped = []
                for j in order:
                    pair = dep[j]
                    mapped.append(tuple((sum((1 << order.index(i) for i in range(d) if side >> i & 1)) for side in (pair[flip[j]], pair[flip[j] ^ 1]))))
                de = tuple(mapped)
                if any((a | b >= 1 << j for j, (a, b) in enumerate(de))):
                    continue
                perm = [2 * order.index(i // 2) + (i % 2 ^ flip[i // 2]) for i in range(2 * k)]
                yield (de, perm)

def run(p, budget):
    done = set()
    stats = Counter()
    for dep, cs in eligible(4, p):
        group = list(transforms(dep, p))
        norm = min((de for de, _ in group))
        if norm in done:
            continue
        done.add(norm)
        autos = [perm for de, perm in group if de == dep]
        maps = [{v: sum((1 << perm[i] for i in range(8) if v >> i & 1)) for v in cs} for perm in autos]
        seen = set()
        for extras in combinations(cs, len(cs) - 12):
            key = min((tuple(sorted((f[v] for v in extras))) for f in maps))
            if key in seen:
                continue
            seen.add(key)
            selected = set(cs) - set(extras)
            ok, data = fit(dep, cs, sorted(selected), p, budget)
            stats[str(ok)] += 1
            print('case', p, dep, extras, ok, dict(stats), flush=True)
            if ok:
                (ROOT / f'witness-{p}-{budget}.json').write_text(json.dumps(data))
                return
    print('final', dict(stats), flush=True)
if __name__ == '__main__':
    run(*map(int, sys.argv[1:]))
