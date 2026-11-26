"""Compare all projected Eulerian/cut pairs, allowing designated overlapping pins."""
from functools import lru_cache
from itertools import combinations, product


@lru_cache(None)
def spaces(n,edges):
    stars = [0]*n
    for i,(u,v) in enumerate(edges):
        stars[u] ^= 1 << i
        stars[v] ^= 1 << i
    cuts = {0}
    for star in stars:
        cuts |= {x ^ star for x in cuts}
    cycles = [x for x in range(1 << len(edges)) if all((x&s).bit_count()%2 == 0 for s in stars)]
    return cycles,cuts


def projections(n,edges,pins,allow_overlap):
    fixed_c = sum(c << i for i,c,d in pins)
    fixed_d = sum(d << i for i,c,d in pins)
    fixed = sum(1 << i for i,c,d in pins)
    free = ((1 << len(edges))-1) ^ fixed
    cycles,cuts = spaces(n,edges)
    return {(c & free,d & free) for c in cycles if c & fixed == fixed_c
            for d in cuts if d & fixed == fixed_d and not(c & d & ~allow_overlap)}


def transformed(n,edges,pins):
    # Test graphs number the free edges first so projections need no reindexing.
    start = len(edges)-len(pins)
    pinned = edges[start:]
    touched = sorted({v for e in pinned for v in e})
    odd = set()
    for (u,v),(_,c,_) in zip(pinned,pins):
        if c:
            odd.symmetric_difference_update({u})
            odd.symmetric_difference_update({v})
    result = set()
    for word in product(range(2), repeat=len(touched)):
        color = dict(zip(touched,word))
        if any(color[u]^color[v] != d for (u,v),(_,_,d) in zip(pinned,pins)):
            continue
        groups = [[v for v in sorted(odd) if color[v]==a] for a in range(2)]
        if any(len(group)%2 for group in groups):
            continue
        new_edges = list(edges[:start])
        new_pins = []
        for group in groups:
            for u,v in zip(group[::2],group[1::2]):
                new_pins.append((len(new_edges),1,0))
                new_edges.append((u,v))
        for v in touched:
            new_pins.append((len(new_edges),0,color[v]))
            new_edges.append((n,v))
        result |= projections(n+1,tuple(new_edges),new_pins,0)
    return result


def audit(n,edges):
    total = 0
    for size in range(1,min(3,len(edges))+1):
        for index in combinations(range(len(edges)),size):
            order = [i for i in range(len(edges)) if i not in index] + list(index)
            reordered = tuple(edges[i] for i in order)
            first = len(edges)-size
            for words in product(range(4),repeat=size):
                pins = [(first+i,w%2,w//2) for i,w in enumerate(words)]
                expected = projections(n,reordered,pins,sum(1<<i for i,c,d in pins))
                assert expected == transformed(n,reordered,pins),(reordered,pins)
                total += 1
    return total


if __name__ == '__main__':
    tested = audit(4,list(combinations(range(4),2)))
    tested += audit(4,[(0,0),(0,1),(0,1),(2,3)])
    print(f"Exact projected tuples agree in {tested} pin configurations (including loops, parallel edges and disconnected graphs).")
