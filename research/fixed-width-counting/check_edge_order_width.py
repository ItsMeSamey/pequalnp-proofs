"""Optimize over all edge/literal orders on tiny simple positive binary CNFs."""
from itertools import combinations, permutations, product
from check_alternation_width import tw, alt_edges


def edge_tw(n,edges):
    g=[0]*n
    for a,b in edges:
        g[a]|=1<<b
        g[b]|=1<<a
    return tw(tuple(g))


def cactus(edges):
    # In a cactus every edge lies on at most one simple cycle.
    for a,b in edges:
        others=[e for e in edges if e!=(a,b)]
        graph={}
        for u,v in others:
            graph.setdefault(u,[]).append(v)
            graph.setdefault(v,[]).append(u)
        stack=[(a,{a})]
        paths=0
        while stack:
            v,seen=stack.pop()
            if v==b:
                paths+=1
                if paths==2:
                    return False
            else:
                stack += [(w,seen|{w}) for w in graph.get(v,[]) if w not in seen]
    return True


def optimum(edges):
    best=len(edges)
    # Alternation is cyclic and reversal invariant: fix first edge+orientation.
    for seq in permutations(edges[1:]):
        for flags in product((False,True),repeat=len(seq)):
            word=edges[0]+sum((e[::-1] if f else e for e,f in zip(seq,flags)),())
            width=tw(alt_edges(word))
            best=min(best,width)
            if not best:
                return best
    return best


if __name__=='__main__':
    records=0
    values={}
    for n in (2,3,4,5):
        edges=list(combinations(range(n),2))
        for m in range(1,min(len(edges),6 if n<=4 else 5)+1):
            for g in combinations(edges,m):
                k=edge_tw(n,g)
                a=optimum(g)
                assert k-3<=a<=k
                assert (a==0)==cactus(g)
                values[k,a]=values.get((k,a),0)+1
                records+=1
    print(records,'graphs;',values)
