"""Check traces of simple-subdivision representatives, ports 0,1,2."""
from itertools import combinations

def signature(edges):
    n = max((v+1 for e in edges for v in e), default=3)
    rows = [0]*n
    for u,v in edges:
        rows[u] |= 1 << v
        rows[v] |= 1 << u
    sig = 0
    for s in range(1<<n):
        odds = sum(1<<v for v in range(n) if s>>v&1 and (s&rows[v]).bit_count()%2)
        if odds not in (3,5,6):
            continue
        sig |= 1 << ((3,5,6).index(odds) + 3*((s&7)==7))
    return sig

star = [(0,3),(1,3),(2,3)]
templates = {
    0: [],
    9: [(0,3),(1,3)],
    59: [(0,3),(2,3),(0,4),(1,4)],
    63: [(1,3),(2,3),(0,4),(2,4),(0,5),(1,5)],
    7: star + [(0,4),(1,5),(2,6)],
    31: [(0,3),(2,4),(3,4),(1,5),(3,5),(0,6)],
    15: star + [(2,4),(0,5),(5,6),(6,7),(7,1)],
}
if __name__ == '__main__':
    from itertools import permutations
    found = set()
    for expected, edges in templates.items():
        assert signature(edges) == expected
        for perm in permutations(range(3)):
            found.add(signature([tuple(perm[v] if v<3 else v for v in e) for e in edges]))
    assert len(found) == 15
    print(sorted(found))
