"""Count ordinary width-nine root tests and check the additional cost-six banks."""
from collections import Counter
from pathlib import Path
from itertools import combinations
import sys
source=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'ordinary-line-nine'
sys.path.insert(0,str(source))
# The imported module optionally accepts a decoder path as its first argument.
sys.argv=sys.argv[:1]
from noand import failures, main, points, lc
from edge import analyze
counts=Counter()
for a,b in combinations([s for s in range(128) if s.bit_count()>=2],2):
    c=(a|b).bit_count()-2+bool(a&b)
    edges=failures(a,b)
    good=all(x & lc[a] & lc[b] for x in points)
    if good:kind='full-good'
    elif not edges:kind='no-edge'
    elif len(edges)==1:kind='one-edge'
    elif len(edges)==2:kind='adjacent' if set(edges[0])&set(edges[1]) else 'disjoint'
    else:raise ValueError(edges)
    counts[c,kind]+=1
    if c==6 and not good:
        assert main(a,b)=='all'
        if edges:assert analyze(a,b)[0]=='all'
for c in range(2,7):
    print(c,*(counts[c,k] for k in ('full-good','no-edge','one-edge','disjoint','adjacent')))
