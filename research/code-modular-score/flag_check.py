#!/usr/bin/env python3
from itertools import combinations
from random import Random

def span(xs):
    s = {0}
    for x in xs:
        s |= {y ^ x for y in s}
    return s

def syndromes(xs):
    s = [0]
    for x in xs:
        s += [y ^ x for y in s]
    return s

def obstruction(cols, u):
    a = [min(x ^ y for y in u) for x in cols]
    if len(span(a)) == 8 and len(set(a) - {0}) == 7:
        return 'F7'
    if len(span(a)) == 16:
        rows = [sum(((x >> j) & 1) << i for i,x in enumerate(a))
                for j in range(max(a).bit_length())]
        if all(x.bit_count() >= 3 for x in span(rows) if x):
            return 'F7*'

def classifier(cols, k):
    u = span(k)
    w = span(cols + k)
    table = {min(v ^ z for z in u): None for v in w}
    for rep in table:
        table[rep] = obstruction(cols, u | {rep ^ z for z in u})
    return lambda v: table[min(v ^ z for z in u)] if v in w else table[0]

def direct(cols, k, v):
    def project(x):
        return x ^ v if x & (1 << max(0, v.bit_length()-1)) else x
    u = span(map(project, k))
    code = [i for i,x in enumerate(syndromes(map(project, cols))) if x in u]
    if len(code) == 8 and all(x.bit_count() == 4 for x in code if x):
        return 'F7*'
    if len(code) == 16:
        dual = [x for x in range(1,128) if all((x & y).bit_count()%2 == 0 for y in code)]
        if len(dual) == 7 and all(x.bit_count() == 4 for x in dual):
            return 'F7'

def main():
    spokes = [1,2,4,8]
    edges = spokes + [a ^ b for a,b in combinations(spokes,2)]
    cols = spokes + [1 ^ x for x in spokes[1:]]
    assert all(direct(list(x), [], 0) is None for x in combinations(edges,7))
    assert classifier(cols,[])(0) is None
    assert classifier(cols,[])(15) == direct(cols,[],15) == 'F7'
    dual = [1,2,4,8,11,13,14]
    assert classifier(dual,[])(0) == direct(dual,[],0) == 'F7*'
    rng = Random(48271)
    count = 0
    for r in range(3,8):
        for _ in range(35):
            cols = [rng.randrange(1 << r) for _ in range(7)]
            k = [rng.randrange(1 << r) for _ in range(rng.randrange(5))]
            test = classifier(cols,k)
            for v in range(1 << r):
                assert test(v) == direct(cols,k,v), (r,cols,k,v)
                count += 1
    print('passed',count,'direction checks and K5/F7* fixtures')

if __name__ == '__main__':
    main()
