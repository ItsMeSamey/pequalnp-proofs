"""Independently minimize the number of products using finite truth-table BFS."""
from collections import deque
from lift import products
from solver import parity,quadratic

checks = 0
for d in range(5):
    for affine in (0,1):
        forms = {sum((parity(m&x)^a)<<x for x in range(1<<d))
                 for m in range(1<<d) for a in range(1+affine)}
        generators = {p&q for p in forms for q in forms}
        distance = {0:0}
        queue = deque([0])
        while queue:
            x = queue.popleft()
            for g in generators:
                y = x^g
                if y not in distance:
                    distance[y] = distance[x]+1
                    queue.append(y)
        for c in range(1+affine):
            for k in range(1<<(d*(d+1)//2)):
                M = [0]*(d+affine)
                if affine:
                    M[d] = c<<d
                pos = 0
                for i in range(d):
                    for j in range(i+1):
                        M[i] |= ((k>>pos)&1)<<j
                        pos += 1
                p,r = products(M,[(1<<d,1)] if affine else [])
                truth = 0
                for x in range(1<<d):
                    real = x | (affine<<d)
                    v = quadratic(M,real)
                    assert v == sum(parity(real&a)*parity(real&b) for a,b in p)%2
                    truth |= v<<x
                assert len(p)==distance[truth]
                checks += 1
print(checks,'product-count optima and every decomposition truth table compared through four free bits')
