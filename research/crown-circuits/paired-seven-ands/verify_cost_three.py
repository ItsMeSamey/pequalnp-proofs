"""Audit coverage by static earliest counts and the two distinct finite searches."""
from collections import Counter,defaultdict
from pathlib import Path
from sys import argv

def rows(name):
    data=Path(name).read_text();assert data.endswith('\n')
    return [list(map(int,row.split())) for row in data.splitlines()]

catalog,first,second=argv[1:]
groups=defaultdict(set)
for i,c,cap,*t in rows(catalog):
    if c!=3 or cap<12:continue
    pins=0
    for continuation in t:pins|=continuation
    earliest=sum(not ((pins>>(2*j))&3) for j in range(len(t)))
    groups[earliest].add(i)
for n,path in [(1,first),(2,second)]:
    r=rows(path);ids={x[0] for x in r}
    assert ids==groups[n] and len(ids)==len(r) and all(x[-1]==0 for x in r)
    print(n,len(ids),sum(x[1] for x in r),'libraries')
assert 0 not in groups
print('analytic',sum(len(ids) for n,ids in groups.items() if n>2))
