"""Direct mask search on every labeled small exterior; no matrix or solver imports."""
from collections import Counter
from itertools import combinations

def bit(i): return 1 << i
def run(m):
    n=m+2
    edges=[(i,j) for i,j in combinations(range(n),2) if i>=2 or j>=2]
    counts=Counter()
    for mask in range(1<<len(edges)):
        rows=[0]*n
        for k,(i,j) in enumerate(edges):
            if mask & bit(k):
                rows[i]|=bit(j)
                rows[j]|=bit(i)
        if not all(r.bit_count()>=3 and r.bit_count()%2 for r in rows[2:]): continue
        for pins in combinations(range(n),2):
            fixed=sum(map(bit,pins))
            # Delete any nonempty set disjoint from pins while retaining oddness at surviving exterior.
            assert any(not cut&fixed and all(cut&bit(v) or not (r&cut).bit_count()%2
                       for v,r in enumerate(rows) if v>=2) for cut in range(1,1<<n))
            counts[sum(i<2 for i in pins)]+=1
    return dict(sorted(counts.items()))

def table(rows):
    cells=set()
    for w in range(1<<len(rows)):
        if any(w&bit(i) and not (rows[i]&w).bit_count()%2 for i in range(2,len(rows))): continue
        for d in range(4):
            if all(not w&bit(i) or ((rows[i]&w).bit_count() + bool(d&bit(i)))%2 for i in (0,1)):
                cells.add((w&3,d))
    return cells
for m in range(1,5):print('exterior sites',m,'by pins on interface',run(m))
examples=[[52,56,41,38,35,31],[30,61,779,7,515,962,800,1312,1252,1140,896]]
for r in examples:
    for state in (0,1):
        if bool(r[0]&2)!=bool(state): r[0]^=2;r[1]^=1
        assert len(table(r))==16
        print(len(r),'physical ab',state,'all sixteen states')
