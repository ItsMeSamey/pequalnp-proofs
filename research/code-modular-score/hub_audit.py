"""Exhaust hub deletion identity on all simple five-node graphs."""
from itertools import combinations
from collections import deque

n = 5
pairs = list(combinations(range(n), 2))

def comps(edges, gone):
    remain = set(range(n)) - gone
    blocks = []
    while remain:
        start = remain.pop()
        part = {start}
        q = deque([start])
        while q:
            u = q.popleft()
            for e in edges:
                if u not in e:
                    continue
                v = e[0] if e[1] == u else e[1]
                if v in remain:
                    remain.remove(v)
                    part.add(v)
                    q.append(v)
        blocks.append(part)
    return blocks

tests = implications = 0
for mask in range(1 << len(pairs)):
    edges = [e for j,e in enumerate(pairs) if mask>>j&1]
    for a,b in pairs:
        if (a,b) in edges:
            continue
        cc = lambda gone: len(comps(edges,gone))
        delta = cc({a,b}) - cc({a}) - cc({b}) + cc(set())
        tests += 1
        if delta > 0:
            implications += 1
            for z in set(range(n))-{a,b}:
                assert any({a,b}<=c for c in comps(edges,{z}))
print(tests, 'hub pairs;', implications, 'positive differences checked')
