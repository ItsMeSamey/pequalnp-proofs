from itertools import combinations, product


def verify(n, edges):
    radix = 2**(n+1)
    zero = even = independent = 0
    for x in product(range(2), repeat=n):
        sums = [1,0,0,0]
        for u,v in edges:
            for _ in range(n+1):
                l = x[u]+x[v]
                sums = [2*sums[i]+sums[(i+l)%4]+sums[(i-l)%4] for i in range(4)]
        zero += sums[0]
        even += sums[0]+sums[2]
        independent += all(not (x[u] and x[v]) for u,v in edges)
    W = 2*zero-even
    recovered = 0
    while W:
        W, digit = divmod(W, radix)
        recovered += digit
    assert recovered == independent


tested = 0
for n in range(1,5):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        verify(n, [e for i,e in enumerate(pairs) if mask >> i & 1])
        tested += 1
print(f'{tested} order-64 digit identities verified')
