from collections import Counter
from itertools import product
from random import Random

def table(rows, offsets, labels):
    out = Counter()
    for mask in range(1 << len(rows)):
        for h in (0, 1):
            if any((mask >> i) & 1 and ((rows[i] & mask).bit_count() + offsets[i] + h) % 2 for i in range(len(rows))):
                continue
            a = 0
            for i, label in enumerate(labels):
                if (mask >> i) & 1:
                    a ^= label
            out[h,mask.bit_count()%2,a] += 1
    return out

def graph(n,r):
    return [r.randrange(1 << n) & ~(1 << i) for i in range(n)]

r=Random(1207)
for it in range(400):
    k=r.randint(1,3)
    ns=[r.randint(1,3) for _ in range(k)]
    offsets=[r.randrange(2) for _ in range(sum(ns))]
    labels=[r.randrange(4) for _ in offsets]
    Q=graph(k,r)
    blocks=[((1<<n)-1)<<sum(ns[:i]) for i,n in enumerate(ns)]
    rows=[]
    children=[]
    for i,n in enumerate(ns):
        start=sum(ns[:i])
        local=graph(n,r)
        ext=sum(blocks[j] for j in range(k) if Q[i]>>j & 1)
        rows.extend((v<<start)|ext for v in local)
        children.append(table(local,offsets[start:start+n],labels[start:start+n]))
    expected=table(rows,offsets,labels)
    got=Counter()
    for h in range(2):
        for z in range(1<<k):
            for aa in product(range(4),repeat=k):
                ways=1
                label=0
                for i,a in enumerate(aa):
                    ways*=children[i][h^((Q[i]&z).bit_count()%2),z>>i & 1,a]
                    label^=a
                if ways:
                    got[h,z.bit_count()%2,label]+=ways
    assert expected==got
print("400 two-bit labeled substitutions checked, including both external fields and parities")
