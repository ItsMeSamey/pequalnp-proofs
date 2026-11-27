"""Exact unweighted Steiner tree, with traceback for the radial disk constructor."""
from heapq import heappop,heappush
from radial_patch import construct


def exact_tree(graph, terminals):
    vertices=len(graph); t=len(terminals); bound=vertices*(t+1)+1
    tables={}; choices={}
    for mask in range(1,1<<t):
        costs=[bound]*vertices; choice=[None]*vertices
        if mask.bit_count()==1:
            v=terminals[mask.bit_length()-1];costs[v]=0;choice[v]=('start',)
        else:
            sub=(mask-1)&mask
            while sub:
                other=mask^sub
                if sub<other:
                    for v,(a,b) in enumerate(zip(tables[sub],tables[other])):
                        if a+b<costs[v]:
                            costs[v]=a+b;choice[v]=('join',sub)
                sub=(sub-1)&mask
        # Multi-source shortest paths relax the last path from a branch to v.
        heap=[]
        for v,cost in enumerate(costs):
            if cost<bound:heappush(heap,(cost,v))
        while heap:
            cost,v=heappop(heap)
            if cost!=costs[v]:continue
            for w in graph[v]:
                if cost+1<costs[w]:
                    costs[w]=cost+1;choice[w]=('edge',v)
                    heappush(heap,(cost+1,w))
        tables[mask]=costs;choices[mask]=choice
    mask=(1<<t)-1;root=terminals[0]
    todo=[(mask,root)];edges=set()
    while todo:
        current,v=todo.pop()
        action=choices[current][v]
        if action is None:raise ValueError("disconnected terminals")
        if action[0]=='edge':
            w=action[1];edges.add(tuple(sorted((v,w))));todo.append((current,w))
        elif action[0]=='join':
            sub=action[1];todo.extend(((sub,v),(current^sub,v)))
    if len(edges)!=tables[mask][root]:
        raise ValueError("Steiner traceback size mismatch")
    return edges


def minimum_patch(dual,rotation):
    return construct(dual,rotation,tree_builder=exact_tree)
