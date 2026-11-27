"""Capped two-port, one-projected-bit saturation and physical-ID relation replay."""
from itertools import combinations, product
from component_nullity import bits
from thick_tag_solver import combine


def paths(edges,labels,u,v):
    out=set()
    def dfs(a,seen,g):
        if a==v:
            out.add(g)
            return
        for j,(b,c) in enumerate(edges):
            if a in (b,c):
                w=a^b^c
                if w not in seen:
                    dfs(w,seen|{w},g^labels[j])
    dfs(u,{u},0)
    return out


def forests(n,edges,labels):
    # Brute construction only for tiny controls. Roots are original vertices 0,1.
    for ids in combinations(range(len(edges)),n-2):
        owner={0:0,1:1}
        gains={0:0,1:0}
        for _ in range(n):
            for j in ids:
                a,b=edges[j]
                if a in owner and b not in owner:
                    owner[b],gains[b]=owner[a],gains[a]^labels[j]
                elif b in owner and a not in owner:
                    owner[a],gains[a]=owner[b],gains[b]^labels[j]
        if len(owner)==n and all(owner[edges[j][0]]==owner[edges[j][1]] and
                                 gains[edges[j][0]]^gains[edges[j][1]]==labels[j] for j in ids):
            yield ids,owner,gains


def check(n,edges,labels,charges):
    full=paths(edges,labels,0,1)
    available={g&1 for g in full}
    for forest,owner,gains in forests(n,edges,labels):
        adjusted=[gains[a]^labels[j]^gains[b] for j,(a,b) in enumerate(edges)]
        options={v&1 for v,(a,b) in zip(adjusted,edges) if owner[a]!=owner[b]}
        if options==available:
            break
    else:
        raise AssertionError("no saturating bipartition")
    assert len(edges)<=8 and n<=6
    has_nontrivial_cycle=False
    for colors in product(range(2),repeat=2):
        for switches in product(range(2),repeat=2):
            color=[colors[owner[i]] for i in range(n)]
            x=[switches[owner[i]]^(gains[i]&1) for i in range(n)]
            active=[j for j,(a,b) in enumerate(edges)
                    if color[a]==color[b] and (labels[j]&1)==x[a]^x[b]]
            assert set(forest)<=set(active)
            # Compare default root connectivity with *all* internal switch and
            # color choices, including assignments that violate the tree default.
            possible=colors[0]==colors[1] and switches[0]^switches[1] in available
            realgain=paths([edges[j] for j in active],[labels[j] for j in active],0,1)
            assert bool(realgain)==possible
            any_assignment=False
            for inner in product(range(4),repeat=n-2):
                ctest=[*colors,*[v>>1 for v in inner]]
                xtest=[*switches,*[v&1 for v in inner]]
                test=[j for j,(a,b) in enumerate(edges) if ctest[a]==ctest[b]
                      and (labels[j]&1)==xtest[a]^xtest[b]]
                if paths([edges[j] for j in test],[labels[j] for j in test],0,1):
                    any_assignment=True
                    break
            assert possible==any_assignment
            physical={}
            for mask in range(1<<len(active)):
                ids=[active[i] for i in bits(mask)]
                boundary=0
                for j in ids:
                    a,b=edges[j]
                    boundary^=(1<<a)^(1<<b)
                if boundary>>2==0:
                    g=0
                    for j in ids:
                        g^=labels[j]
                    physical.setdefault((boundary,g),ids)
            # Eliminate tree edges at interior vertices. Each retained physical
            # chord contributes its adjusted full gain and owner boundary.
            virtual={(0,0)}
            for j in active:
                if j not in forest:
                    a,b=edges[j]
                    bd=(1<<owner[a])^(1<<owner[b])
                    virtual|={(u^bd,g^adjusted[j]) for u,g in virtual}
            assert virtual==set(physical)
            has_nontrivial_cycle |= (0,2) in virtual
            # Exclude both boundary vertices, which are charged at the torso.
            folded=[0,0]
            offset=0
            parts=[0,0]
            moment=0
            for i in range(2,n):
                folded[owner[i]]^=charges[i]
                if gains[i]&1:
                    offset^=charges[i]
                parts[color[i]]^=charges[i]
                if x[i]:
                    moment^=charges[i]
            assert parts==[combine(folded,sum(1<<i for i in range(2) if colors[i]==j))
                           for j in range(2)]
            assert moment==offset^combine(folded,sum(1<<i for i in range(2) if switches[i]))
    return available,has_nontrivial_cycle


if __name__=="__main__":
    # Three disjoint paths; the two gain-even paths have different full gains.
    edges=[(0,2),(2,1),(0,3),(3,1),(0,4),(4,1)]
    gains=[1,1,0,1,3,1]
    opts,nontriv=check(5,edges,gains,[3,5,1,6,7])
    assert opts=={0,1} and nontriv
    # Include a cycle confined to one root side and duplicate physical edges.
    side=[(0,2),(2,1),(2,3),(3,4),(4,2),(0,2),(4,4)]
    for s in range(8):
        g=[1,3,1,1,2,s&3,2]
        check(5,side,g,[s,2,3,7,1])
    print("9 indexed hosts, 144 root color/switch assignments; theta options and full kernel gain checked")
