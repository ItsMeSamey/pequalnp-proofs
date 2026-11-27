"""Disjoint status counts for a deterministic catalogue of physical prefixes."""
from collections import Counter
from functools import reduce
from operator import or_
from random import Random
from h5_three_sink_leak_sets import CASES, EDGES, N

def catalogue():
    rng = Random(9822)
    rows = set()
    for _ in range(2000):
        labels = list(range(10))
        rng.shuffle(labels)
        petals = [labels[:3]]
        for start in (3,5,7):
            petals.append([rng.choice(labels[:start]), *labels[start:start+2]])
        rng.shuffle(petals)
        a,b,c,d = [sum(1 << i for i in petal) for petal in petals]
        rows.add((*sorted((a,b)), *sorted((c,d))))
    return sorted(rows)

def outcomes(scopes, indices):
    a,b,c,d = scopes
    block = a | b | c | d
    assert block.bit_count() == 9
    omitted = 1023 ^ block
    def evaluate(row):
        return int(bool(a & row and b & row)) + 2*int(bool(c & row and d & row))
    positives = tuple(map(evaluate, EDGES))
    negatives = tuple(map(evaluate, N))
    if any(reduce(or_, trace) != 3 for trace in (positives, negatives)):
        return ['safe_or_unproductive'] * len(indices)
    result = []
    for ix in indices:
        leak = CASES[ix]
        available = 3 ^ reduce(or_, (negatives[i] for i in leak))
        raw = 1023 ^ reduce(or_, (N[i] for i in leak))
        best = 99
        for hidden in (1,2,3):
            if hidden & available != hidden:
                continue
            choices = [edge & raw for edge,p in zip(EDGES, positives) if not p & hidden]
            if 0 in choices:
                continue
            if not choices:
                nraw = 0
            elif all(e & block for e in choices) or all(e & omitted for e in choices):
                nraw = 1
            else:
                nraw = 2
            best = min(best, hidden.bit_count()+nraw)
        result.append('no_U' if best == 99 else 'budget' if best >= 3 else 'unknown')
    return result

if __name__ == '__main__':
    import sys
    indices = list(map(int,sys.argv[1:]))
    counts = [Counter() for _ in indices]
    rows = catalogue()
    for scopes in rows:
        for counter,status in zip(counts,outcomes(scopes,indices)):
            counter[status] += 1
    print('unique_chronological_prefixes',len(rows))
    for index,counter in zip(indices,counts):
        assert sum(counter.values()) == len(rows)
        print(index,*[counter[s] for s in ('safe_or_unproductive','no_U','budget','unknown')])
