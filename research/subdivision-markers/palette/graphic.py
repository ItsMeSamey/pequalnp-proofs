from finite import *
import json
from itertools import combinations
from functools import lru_cache
need={int(k) for k in json.load(open('single-gadgets.json')) if not int(k)>>sid[frozenset([0,7])]&1}
@lru_cache(None)
def join(p,a,b): return tuple(x if x!=p[b] else p[a] for x in p)
@lru_cache(None)
def trace(p):
    p=p[:4]
    return 1<<sid[frozenset(x for x in W if all(sum((x>>i)&1 if i<3 else x.bit_count()%2 for i in range(4) if p[i]==v)%2==0 for v in set(p)))]
ans={}
for n in range(4,7):
    edges=list(combinations(range(n),2)); start=tuple(range(n))
    for m in range(n-1,8):
        for pairs in combinations(edges,m):
            if n>4 and any(sum(j in e for e in pairs)<3 for j in range(4,n)): continue
            states={start}
            for a,b in pairs: states|={join(p,a,b) for p in states}
            h=0
            for p in states: h|=trace(p)
            if h in need and (h not in ans or m<len(ans[h])): ans[h]=pairs
    print(n,len(ans),'of',len(need),flush=True)
print('missing',sorted(need-set(ans)))
from pathlib import Path
from collections import Counter
assert set(ans)==need
assert all(max(max(e) for e in es)<=4 for es in ans.values())
print('edge counts',sorted(Counter(map(len,ans.values())).items()))
Path(__file__).with_name('graphic-gadgets.json').write_text(json.dumps(ans,sort_keys=True)+'\n')
