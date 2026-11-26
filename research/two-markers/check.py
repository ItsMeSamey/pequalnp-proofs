from itertools import product
from collections import deque
from random import Random


def witness(adj, labels, target):
    if target == 0:
        return 0
    if target in labels:
        return 1 << labels.index(target)
    a,b = [k for k in (1,2,3) if k != target]
    for u in range(len(adj)):
        if labels[u] != a:
            continue
        for v in range(len(adj)):
            if labels[v] != b:
                continue
            edge = 1 << v
            if not adj[u]&edge:
                return (1<<u) | edge
            seen = (1<<u) | edge
            queue = deque([(u, 1<<u)])
            while queue:
                w,path = queue.popleft()
                if w!=u and adj[w]&edge:
                    return path | edge
                for z,color in enumerate(labels):
                    bit = 1<<z
                    if color==0 and adj[w]&bit and not seen&bit:
                        seen |= bit
                        queue.append((z, path|bit))
    return None


def check(adj,labels):
    n=len(adj)
    outputs=set()
    for s in range(1<<n):
        if all(not (s>>i&1) or (row&s).bit_count()%2==0 for i,row in enumerate(adj)):
            label=0
            for i in range(n):
                if s>>i&1:label ^= labels[i]
            outputs.add(label)
    for target in range(4):
        s=witness(adj,labels,target)
        assert (s is not None)==(target in outputs)
        if s is not None:
            assert all(not(s>>i&1) or (row&s).bit_count()%2==0 for i,row in enumerate(adj))
            label=0
            for i in range(n):
                if s>>i&1:label^=labels[i]
            assert label==target

def graph(n, code):
    adj=[0]*n
    for i in range(n):
        for j in range(i):
            if code&1:
                adj[i]|=1<<j
                adj[j]|=1<<i
            code >>= 1
    return adj

if __name__=='__main__':
    cases=0
    for n in range(5):
        for code in range(1<<(n*(n-1)//2)):
            for labels in product(range(4),repeat=n):
                check(graph(n,code),labels)
                cases += 1
    rng=Random(33631)
    for _ in range(800):
        n=rng.randrange(5,10)
        check(graph(n,rng.getrandbits(n*(n-1)//2)),[rng.randrange(4) for _ in range(n)])
    print(cases,'exhaustive and 800 random cases passed.')
