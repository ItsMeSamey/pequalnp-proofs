from few_groups import check
from itertools import combinations
graphs=[(3,5,6),(5,6),(3,5)]
for edges in graphs:
    raws=[]
    for i in range(3):raws +=[1<<i]*(3-sum(e>>i&1 for e in edges))
    raws +=[0]*(13-len(raws)-len(edges))
    found=False
    for k in range(0,6):
        for extras in sorted(set(combinations(raws,k)),key=lambda a:(a.count(0),a)):
            if len(edges)+k<2:continue
            if check(3,edges+extras,1500,True) is False:
                print(edges,extras,'UNSAT',flush=True);found=True;break
        if found:break
    if not found:print(edges,'open',flush=True)
