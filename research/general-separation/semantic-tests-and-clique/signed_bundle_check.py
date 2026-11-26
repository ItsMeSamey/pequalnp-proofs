"""Check each bundled sign and the exact integer tour count on labeled arcs."""
from collections import Counter
from itertools import permutations, product
from random import Random


def inv(seq):
    return sum(x > y for i,x in enumerate(seq) for y in seq[i+1:]) % 2


def chunks(arcs, endpoint, width):
    order = sorted(range(len(arcs)),key=lambda e:(arcs[e][endpoint],e))
    return {e:i//width for i,e in enumerate(order)}


def bundled(arcs, marked, a, b):
    tail = sorted(marked,key=lambda e:(arcs[e][0],e))
    head = sorted(marked,key=lambda e:(arcs[e][1],e))
    local = sum(inv([(b[e],e) for e in tail if a[e] == i]) for i in set(a.values()))
    local += sum(inv([(a[e],e) for e in head if b[e] == j]) for j in set(b.values()))
    parity = Counter((a[e],b[e]) for e in marked)
    crossed = sum((p%2)*(q%2) for (i,j),p in parity.items()
                  for (k,l),q in parity.items() if i<k and j>l)
    return (local+crossed)%2


def check(n, arcs, rng, stats):
    by_tail = [[i for i,(u,v) in enumerate(arcs) if u==j] for j in range(n)]
    direct = 0
    for order in permutations(range(1,n)):
        path=(0,)+order
        possible=1
        for u,v in zip(path,path[1:]+(0,)):
            possible *= arcs.count((u,v))
        direct+=possible
    layouts = [(chunks(arcs,0,wa),chunks(arcs,1,wb)) for wa,wb in
               [(1,1),(2,3),(3,2),(max(1,len(arcs)),max(1,len(arcs))),
                (rng.randrange(1,6),rng.randrange(1,6))]]
    count=0
    for cover in product(*by_tail):
        succ=[arcs[e][1] for e in cover]
        if len(set(succ))!=n:
            continue
        stats['covers']+=1
        for mask in range(0,1<<n,2):
            if any(((mask>>u)^(mask>>v))&1 for u,v in enumerate(succ)):
                continue
            marked = [cover[u] for u in range(n) if mask>>u&1]
            ref = inv([arcs[e][1] for e in marked])
            for a,b in layouts:
                assert bundled(arcs,marked,a,b)==ref, (arcs,cover,mask,a,b)
                stats['sign_tests']+=1
            count+=(-1)**(len(marked)+ref)
    assert count==direct,(arcs,count,direct)
    stats['graphs']+=1
    stats['labeled_tours']+=direct
    stats['parallel_graphs']+=len(set(arcs))<len(arcs)
    stats['loop_graphs']+=any(u==v for u,v in arcs)


def main():
    rng=Random(7461)
    stats=Counter()
    for n in range(1,8):
        # Parallel padding at high-degree hubs splits vertex incidence lists over chunks.
        for _ in range(18):
            base=list(range(n))
            rng.shuffle(base)
            arcs=list(enumerate(base))
            arcs += [(rng.randrange(n),rng.randrange(n)) for _ in range(n+2)]
            arcs += [(0,rng.randrange(n)),(rng.randrange(n),0),arcs[0]]
            rng.shuffle(arcs)
            check(n,arcs,rng,stats)
    for mask in range(1<<9):
        check(3,[(i//3,i%3) for i in range(9) if mask>>i&1],rng,stats)
    print(dict(sorted(stats.items())))


if __name__=='__main__':
    main()
