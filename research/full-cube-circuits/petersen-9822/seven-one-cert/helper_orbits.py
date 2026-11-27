"""Choose one primitive-pair helper per orbit of the physical signed axes."""
from itertools import combinations
from pathlib import Path
from functools import reduce
from operator import or_
def data(row):
    F=(1<<128)-1
    B=[]
    for j,u in enumerate(row):
        side=sum(1<<x for x in range(128) if x>>j&1)
        B.extend([u&side,u&~side])
    traces={}
    for x in range(128):
        traces.setdefault(tuple(m>>x&1 for m in B),x)
    points=list(traces.values())
    def compact(m):return sum(((m>>x)&1)<<i for i,x in enumerate(points))
    primitive=set(B)
    helpers={0}|{a|b for a,b in combinations(B,2) if a|b not in primitive and a|b!=F}|(set(row)-{F}-primitive)
    helpers=sorted(helpers,key=compact)
    orbit=list(range(len(helpers)))
    def root(i):
        while orbit[i]!=i:i=orbit[i]
        return i
    transforms=[]
    for j in range(7):
        transforms.append(([x^(1<<j) for x in range(128)],list(range(7))))
        for k in range(j):
            perm=list(range(7));perm[j],perm[k]=k,j
            transforms.append(([x^(((x>>j^x>>k)&1)*((1<<j)|(1<<k))) for x in range(128)],perm))
    for perm, axes in transforms:
        def act(m):return sum(1<<perm[x] for x in range(128) if m>>x&1)
        if any(act(u)!=row[axes[j]] for j,u in enumerate(row)):continue
        for i,h in enumerate(helpers):
            a,b=root(i),root(helpers.index(act(h)))
            orbit[max(a,b)]=min(a,b)
    return [root(i) for i in range(len(helpers))]
if __name__=='__main__':
    for row in Path('full6.tsv').read_text().splitlines():
        r=data(list(map(int,row.split())))
        print(*sorted(set(r)))
