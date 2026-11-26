from itertools import combinations
from functools import reduce
from operator import xor

def image(rows):
    space = {0}
    for row in rows:
        space |= {x ^ row for x in space}
    return space

def forests(n, edges):
    for es in combinations(edges, n-3):
        parts = [{i} for i in range(n)]
        for u,v in es:
            left = next(c for c in parts if u in c)
            right = next(c for c in parts if v in c)
            if left == right:
                break
            parts.remove(right)
            left.update(right)
        else:
            yield sorted(parts,key=min)

def sign(a,b):
    return (-1)**((a&b).bit_count()%2)

# Walsh character sum factors into two independent 16-term sums.
walsh = [[sum(sign(h, x^y) for h in range(16)) for y in range(16)] for x in range(16)]
planes = {frozenset(image([a,b])) for a in range(1,16) for b in range(a+1,16)}
for n in [4,6]:
    edges = list(combinations(range(n),2))
    dense = [1,2,4,8,7][:n-1]
    dense.append(reduce(xor,dense))
    count = 0
    for parts in forests(n, edges):
        scores = [reduce(xor,(dense[i] for i in c),0) for c in parts]
        for p in planes:
            checksum = sum(walsh[scores[0]][a]*walsh[scores[1]][b]
                           for a in p-{0} for b in p-{0,a})
            assert checksum == 256 * (image(scores)==p)
        if n >= 5:
            labels = [0]*n
            for bit,(x,y) in enumerate([(0,1),(2,3),(0,4),(2,4)]):
                labels[x] ^= 1<<bit
                labels[y] ^= 1<<bit
            actual = image([reduce(xor,(labels[i] for i in c),0) for c in parts])
            owner = {v:i for i,c in enumerate(parts) for v in c}
            correct = owner[0]==owner[1] and owner[2]==owner[3] and len({owner[i] for i in (0,2,4)})==3
            assert (actual=={0,4,8,12})==correct
        count += 1
    print('K',n,'forests',count,'planes',len(planes))
# Prism K4 substitution example: action is on shortened cut code, different input type.
rows = [sum(1<<(3*i+j) for j in range(3)) for i in range(3)]
rows += [sum(1<<(3*i+j) for i in range(3)) for j in range(3)]
code = image(rows)
Y=78
assert {w for w in code if w&~Y==0}=={0,78}
scores={(((w&10).bit_count()%2)|(((w&4).bit_count()%2)<<1)) for w in code if w&~Y==0}
assert scores=={0,2}
print('prism mask 78: exact shortened score line {0,2}')
