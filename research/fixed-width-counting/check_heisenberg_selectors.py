from itertools import combinations, product


def mul(x, y):
    a,b,c = x
    d,e,f = y
    return ((a+d)%3, (b+e)%3, (c+f+a*e)%3)


def check_commutator():
    for x,z in product(range(2), repeat=2):
        for sign in (-1, 1):
            value = (0,0,0)
            for step in [(sign*z,0,0),(0,x,0),(-sign*z,0,0),(0,-x,0)]:
                value = mul(value, step)
            assert value == (0,0,(sign*z*x)%3)


def count(n, edges):
    t = n//2+1
    zeros = covers = 0
    for x in product(range(2), repeat=n):
        counts = [1,0,0]
        for u,v in edges:
            for _ in range(t):
                nxt = [0,0,0]
                for r,k in enumerate(counts):
                    for a,b in product(range(2), repeat=2):
                        nxt[(r+(a-b)*(x[u]+x[v]))%3] += k
                counts = nxt
        zeros += counts[0]
        covers += all(x[u] or x[v] for u,v in edges)
    return ((3*zeros-(1 << (n+2*t*len(edges))))//2) % (4**t), covers


check_commutator()
total = 0
for n in range(1,6):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [e for i,e in enumerate(pairs) if mask >> i & 1]
        recovered, exact = count(n, edges)
        assert recovered == exact
        total += 1
print(f'{total} Heisenberg-to-cover identities verified')
