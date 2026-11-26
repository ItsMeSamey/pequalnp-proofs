from collections import deque
from itertools import combinations, product
from math import comb, prod
from random import Random

rng = Random(4321)

def check(n, labels):
    pairs = list(combinations(range(n), 2))
    edges = [(i,j,e) for (i,j),mask in zip(pairs,labels) for e in (0,1) if mask & (1<<e)]
    shift = [None]*n
    parts = []
    for v in range(n):
        if shift[v] is not None:
            continue
        shift[v] = 0
        stack, vertices, balanced = [v], [], True
        while stack:
            x = stack.pop()
            vertices.append(x)
            for i,j,e in edges:
                if x != i and x != j:
                    continue
                y = j if x == i else i
                a = shift[x]^e
                if shift[y] is None:
                    shift[y] = a
                    stack.append(y)
                elif shift[y] != a:
                    balanced = False
        parts.append((vertices, balanced))

    def profile(word):
        res = []
        for vertices, balanced in parts:
            bits = [word[i]^shift[i] for i in vertices if word[i]!=2]
            r,q = len(bits),sum(bits)
            res.append((r,q if balanced else (q%2 if r==len(vertices) else -1)))
        return tuple(res)

    words = set(product(range(3),repeat=n))
    seen = set()
    assignments = list(product(range(2),repeat=n))
    while words:
        seed = words.pop()
        signature = profile(seed)
        assert signature not in seen
        seen.add(signature)
        orbit = [seed]
        for w in orbit:
            for i,j,e in edges:
                arr = list(w)
                arr[i] = w[j]^e if w[j]!=2 else 2
                arr[j] = w[i]^e if w[i]!=2 else 2
                candidate = tuple(arr)
                if candidate in words:
                    words.remove(candidate)
                    orbit.append(candidate)
        assert all(profile(w)==signature for w in orbit)
        count = 0
        for x in assignments:
            possible = all((q<=h<=len(v)-r+q if bal else q<0 or q==h)
                           for (r,q),(_,h),(v,bal) in zip(signature,profile(x),parts))
            brute = any(all(a==2 or a==b for a,b in zip(w,x)) for w in orbit)
            assert possible == brute
            count += possible
        mult = 1
        for (r,q),(v,bal) in zip(signature,parts):
            s = len(v)
            mult *= (sum(comb(s,h) for h in range(q,s-r+q+1)) if bal
                     else 2**(s-(q>=0)))
        assert mult == count

num = 0
for n in (1,2,3,4,5):
    size = n*(n-1)//2
    for labels in (product(range(4),repeat=size) if n<=3 else
                   [tuple(rng.randrange(4) for _ in range(size)) for _ in range(50)]):
        check(n,labels)
        num += 1
print(f"{num} signed multigraphs, all partial and complete words checked")
