from collections import Counter
from itertools import combinations
edges=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
pairs=[1<<a|1<<b for a,b in edges]
def star_cost(rest):
    induced=[e for e in pairs if e&rest==e]
    if not induced:return 0
    vertices=[i for i in range(10) if rest>>i&1]
    for k in range(1,len(vertices)+1):
        for subset in combinations(vertices,k):
            mask=sum(1<<i for i in subset)
            if all(e&mask for e in induced):return len(induced)+k-1
for s in range(1,11):
    costs=Counter(star_cost(1023^mask) for mask in range(1024) if mask.bit_count()==s)
    ruled=sum(n for c,n in costs.items() if c<s-1)
    repair=sum(n for c,n in costs.items() if c<=s)
    print(s,dict(sorted(costs.items())),ruled,repair)
