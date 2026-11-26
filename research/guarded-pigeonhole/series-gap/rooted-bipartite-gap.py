from pathlib import Path
import runpy
src=Path(__file__).parent
raw=runpy.run_path(str(src/'rooted-gap.py'))
graph=[554,3589,282,5,1892,1617,3504,2368,1748,1331,882,194]
edges=[(4,5),(6,7),(4,8),(0,9),(6,10),(9,10),(1,11)]
for i,j in edges:
    k=len(graph);graph[i]^=(1<<j)|(1<<k);graph[j]^=(1<<i)|(1<<k);graph.append((1<<i)|(1<<j))
weight=286;rhs=1
if __name__=='__main__':
    n=len(graph);table=runpy.run_path(str(src/'general-rooted.py'))['tables']
    allbits,masks=table(n-2);models=allbits
    for i,row in enumerate(graph):
        nb=0
        for j in range(n):
            if (row>>j)&1:nb^=masks[j]
        models &= allbits^(masks[i]&nb)
    actual=0
    for i in range(n):
        if weight>>i&1:actual^=masks[i]
    assert models and not(models&(~actual if rhs else actual))
    cut=2362
    for j,(u,v) in enumerate(edges,12):cut |= (1^((cut>>u)&1))<<j
    assert all(not(nb & (cut if cut>>i&1 else ~cut)) for i,nb in enumerate(graph))
    print("Adjacency masks",graph,"cut",cut,"sizes",cut.bit_count(),n-cut.bit_count(),"models",models.bit_count(),flush=True)
    for d in (2,3,4):
        for op in (False,True):
            print(d,'opposite' if op else 'direct',raw['prove'](graph,d,op,weight,rhs),flush=True)
