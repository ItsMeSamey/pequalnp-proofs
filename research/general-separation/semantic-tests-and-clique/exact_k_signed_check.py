"""Independent canonical-color and rootless-cycle cancellation tests."""
from collections import Counter
from itertools import permutations, product
from random import Random


def cycles(p):
    unseen = set(range(len(p)))
    ans = 0
    while unseen:
        i = next(iter(unseen))
        ans += 1
        while i in unseen:
            unseen.remove(i)
            i = p[i]
    return ans


def verify(n,arcs,stats):
    out = sorted(range(len(arcs)),key=lambda i:(arcs[i][0],i))
    rows = [[e for e in out if arcs[e][0]==j] for j in range(n)]
    direct, sums = Counter(),Counter()
    for p in permutations(range(n)):
        mult = 1
        for i,v in enumerate(p):
            mult *= arcs.count((i,v))
        direct[cycles(p)] += mult
    for selected in product(*rows):
        p = [arcs[e][1] for e in selected]
        if len(set(p))!=n:
            continue
        for k in range(1,n+1):
            for color in product(range(k),repeat=n):
                if any(color[i]!=color[v] for i,v in enumerate(p)):
                    continue
                anchors = set()
                seen = set()
                for i,c in enumerate(color):
                    if c not in seen:
                        if c != len(seen):
                            break
                        anchors.add(i)
                        seen.add(c)
                else:
                    if len(seen)!=k:
                        continue
                    for width in (1,2,5):
                        register=0
                        roots=set()
                        for left in range(0,len(out),width):
                            for e in out[left:left+width]:
                                v=arcs[e][0]
                                if e==rows[v][-1]:
                                    c=color[v]
                                    if not (register>>c)&1:
                                        assert c==register.bit_count()
                                        roots.add(v)
                                        register |= 1<<c
                        assert roots==anchors and register==(1<<k)-1
                    for mask in range(1<<n):
                        if any(mask>>i&1 for i in anchors):
                            continue
                        if any(((mask>>i)^(mask>>j))&1 for i,j in enumerate(p)):
                            continue
                        marked=[p[i] for i in range(n) if mask>>i&1]
                        inv=sum(u>v for i,u in enumerate(marked) for v in marked[i+1:])
                        sums[k]+=(-1)**(len(marked)+inv)
                        stats['signed_terms']+=1
    assert all(direct[k]==sums[k] for k in range(1,n+1)),(arcs,direct,sums)
    stats['graphs']+=1
    stats['coefficient_tests']+=n


if __name__=='__main__':
    rng=Random(719)
    stats=Counter()
    for mask in range(512):
        verify(3,[(i//3,i%3) for i in range(9) if mask>>i&1],stats)
    for n in range(1,6):
        for i in range(7):
            p=list(range(n))
            rng.shuffle(p)
            arcs=list(enumerate(p))
            arcs += [(rng.randrange(n),rng.randrange(n)) for _ in range(n)]
            arcs += [arcs[0]]
            rng.shuffle(arcs)
            verify(n,arcs,stats)
    for n in range(1,6):
        for p in permutations(range(n)):
            for q in permutations(range(n)):
                assert (cycles([q.index(i) for i in p])==n)==(p==q)
                stats['interface_entries']+=1
    print(dict(sorted(stats.items())))
