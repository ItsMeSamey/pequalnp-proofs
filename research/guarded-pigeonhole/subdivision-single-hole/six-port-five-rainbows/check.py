from itertools import permutations, product

def colorable(rows, boundary):
    n = len(rows)
    edges = [(i, n+j) for i, row in enumerate(rows) for j in range(n) if row >> j & 1]
    ports = [v for v in range(2*n) for _ in range(3-sum(v in e for e in edges))]
    masks = [0]*(2*n)
    for v, c in zip(ports, boundary):
        if masks[v] & (1<<c):
            return False
        masks[v] |= 1<<c
    def search(remaining):
        if not remaining:
            return True
        u, v = remaining[0]
        for c in range(3):
            bit = 1<<c
            if (masks[u] | masks[v]) & bit:
                continue
            masks[u] ^= bit
            masks[v] ^= bit
            if search(remaining[1:]):
                return True
            masks[u] ^= bit
            masks[v] ^= bit
        return False
    return search(edges)

def canonical(word):
    labels = {}
    return tuple(labels.setdefault(c, len(labels)) for c in word)

def census(rows):
    return {word for word in product(range(3), repeat=6)
            if canonical(word) == word and colorable(rows, word)}


rows = [9,10,24,21,22]
table = census(rows)
minorities = {canonical(tuple(int(k in (i,j)) for k in range(6)))
              for i in range(3) for j in range(3,6)}
rainbows = {(0,1,2)+p for p in permutations(range(3))}
missing = (0,1,2,1,0,2)
print(len(table), sorted(table))
assert table & rainbows == rainbows - {missing}
assert minorities <= table
assert table == minorities | (rainbows - {missing})
