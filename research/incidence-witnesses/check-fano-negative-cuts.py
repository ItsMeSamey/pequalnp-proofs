"""Check the negative conflict clique, restricted cover sizes, and weight bound."""
from itertools import combinations
from collections import Counter
from math import log2
from pathlib import Path
import runpy
rows=runpy.run_path(str(Path(__file__).parent/'fano20-canonical'/'encode.py'))['cases']()
flags=[mask for mask,pos in rows if pos]
neg=[mask for mask,pos in rows if not pos]
assert all(any((a|b)&f==f for f in flags) for a,b in combinations(neg,2))
covers=[c for c in range(1<<12) if all(c&f for f in flags)]
tau=[min(c.bit_count() for c in covers if not c&n) for n in neg]
assert Counter(tau)=={8:17,7:4}
weight=sum(2**(v-1) for v in tau)
assert weight==2432
print(f'{len(neg)} negatives, 210 incompatible pairs; tau=8 on 17 and 7 on 4; mean hot cap {20-log2(weight):.9f}')
for k in (1,2):
    hits=[]
    for sites in combinations(range(12),k):
        mask=sum(1<<s for s in sites)
        if not any(mask&f==f for f in flags):
            hits.append(sum(mask&n==mask for n in neg))
    print(k,dict(sorted(Counter(hits).items())))
