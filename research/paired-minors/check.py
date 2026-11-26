from itertools import combinations
from random import Random


def determinant(rows, selected):
    pivots = {}
    for i, row in enumerate(rows):
        if selected >> i & 1:
            v = row & selected
            while v:
                k = v.bit_length()
                if k not in pivots:
                    pivots[k] = v
                    break
                v ^= pivots[k]
            else:
                return 0
    return 1


def gadget(sets, universe):
    occurrences = [(j, a) for j, subset in enumerate(sets) for a in subset]
    m = len(occurrences)
    n = m + universe
    P, Q = [0]*n, [0]*n
    cycles = [[i for i,(k,a) in enumerate(occurrences) if k == j]
              for j in range(len(sets))]
    cycles.append(list(range(m, n)))
    for group in cycles:
        for i, nxt in zip(group, group[1:] + group[:1]):
            P[i] = 1 << nxt
    for i, (_,a) in enumerate(occurrences):
        Q[m+a] |= 1 << i
        Q[i] = 1 << (m+a)
    altered = Q[:]
    altered[m] = 0
    return P,Q,altered


def run():
    cases = 0
    for u in range(1,4):
        subsets = [tuple(i for i in range(u) if s>>i&1) for s in range(1,1<<u)]
        for r in range(min(4,len(subsets))+1):
            for family in combinations(subsets,r):
                P,Q,R=gadget(family,u)
                different = any(determinant(P,s) and determinant(Q,s)!=determinant(R,s)
                                for s in range(1<<len(P)))
                exact = any(all(sum(v in subset for subset in cover)==1 for v in range(u))
                            for size in range(r+1) for cover in combinations(family,size))
                assert different == exact
                cases += 1
    print(cases, 'exact-cover systems checked')
if __name__ == '__main__':
    run()
