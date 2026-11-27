"""Three or more prescribed pins in the simple line graph of a loopless multigraph."""
from itertools import combinations
from solver import extend

def solve_multi(n, edges, pins):
    bundles={}
    for i,(u,v) in enumerate(edges):
        if u==v: raise ValueError('root must be loopless')
        bundles.setdefault(tuple(sorted((u,v))),[]).append(i)
    skeleton=list(bundles)
    pins=set(pins)
    required={i:pins.intersection(bundles[e]) for i,e in enumerate(skeleton) if pins.intersection(bundles[e])}
    terminals=sorted({x for i in required for x in skeleton[i]})
    vertices=set(range(n))
    for mask in range(1<<len(terminals)):
        odd_ends={x for j,x in enumerate(terminals) if mask>>j&1}
        even_ends=set(terminals)-odd_ends
        odd_req=set()
        even_req=set()
        restored=set(pins)
        for i,need in required.items():
            u,v=skeleton[i]
            weight=1^(u in odd_ends)^(v in odd_ends)
            if len(need)%2!=weight:
                extra=next((j for j in bundles[skeleton[i]] if j not in need),None)
                if extra is None: break
                restored.add(extra)
            if weight:
                (odd_req if u in odd_ends else even_req).add(i)
        else:
            defects=set(odd_ends)
            for i in odd_req:
                defects.symmetric_difference_update(skeleton[i])
            optional=vertices-odd_ends-even_ends
            for size in range(min(len(defects),len(optional))+1):
                for extra in combinations(optional,size):
                    support=odd_ends.union(extra)
                    odd=extend(skeleton,support,odd_req,True)
                    if odd is None: continue
                    even=extend(skeleton,vertices-support,even_req,False)
                    if even is not None:
                        return restored|{bundles[skeleton[i]][0] for i in (odd|even)-required.keys()}
    return None
