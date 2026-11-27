"""Translated branch for a signed dense simple graph with bounded defect cover.

solve returns original indexed support IDs or None for an injective translated
witness. The pure branch is separate. See signed-dense-all-traces.md.
"""
from itertools import combinations, product
from component_nullity import bits, dependencies, trace
from thick_tag_solver import basis, combine


def solve(n, edges, q, z, named, cover, target):
    """z is an original edge mask, switchable to zero off the given vertex cover."""
    edges, q, named = list(edges), list(q), list(named)
    cover, target = tuple(cover), frozenset(target)
    N = len(edges)
    if (type(n) is not int or n < 1 or len(q)!=N or len(named)!=N
            or type(z) is not int or z < 0 or z >> N
            or any(type(v) is not int or v<0 for v in q)
            or any(type(v) is not int or not 0<=v<64 for v in named)
            or any(type(v) is not int or not 0<=v<n for v in cover)
            or len(set(cover))!=len(cover)
            or any(type(t) is not int or not 0<=t<64 for t in target)):
        raise ValueError("invalid dense-cover input")
    h = len(basis(sorted(target))[1])
    if len(target)!=1<<h:
        raise ValueError("target is not a binary subspace")
    adj = [{} for _ in range(n)]
    cuts = [0]*n
    for i,(a,b) in enumerate(edges):
        if (type(a) is not int or type(b) is not int or not 0<=a<n or not 0<=b<n
                or a==b or b in adj[a]):
            raise ValueError("expected simple indexed graph")
        adj[a][b]=adj[b][a]=i
        cuts[a] |= 1<<i
        cuts[b] |= 1<<i
    if (len(basis(cuts)[1])!=n-1 or len(basis(cuts+[z])[1])!=n
            or len(dependencies(q))!=n or any(combine(q,w) for w in cuts+[z])):
        raise ValueError("kernel is not the connected cut space plus independent z")
    cov=set(cover)
    outside=tuple(i for i in range(n) if i not in cov)
    # Normalize the original sign by an actual cut, component by component.
    x={}
    for root in outside:
        if root in x:
            continue
        x[root]=0
        todo=[root]
        while todo:
            a=todo.pop()
            for b,edge in adj[a].items():
                if b in cov:
                    continue
                value=x[a]^((z>>edge)&1)
                if b not in x:
                    x[b]=value
                    todo.append(b)
                elif x[b]!=value:
                    raise ValueError("defect is not switchable onto supplied cover")
    for v,value in x.items():
        if value:
            z ^= cuts[v]
    if h==0:
        return None
    cutoff=2*max(n-1-len(neighbors) for neighbors in adj)
    charges=[combine(named,w) for w in cuts]
    zgain=combine(named,z)
    bins=tuple(range(2*h))  # bin = 2*part + switch bit
    def zero(a,b,la,lb):
        edge=adj[a].get(b)
        return (la//2==lb//2 and edge is not None
                and not (((z>>edge)^la^lb)&1))

    def test(fixed,remaining,large):
        count=len(large)
        if len(remaining)<(cutoff+1)*count or (remaining and not large):
            return None
        gain=[0]*h
        sw=0
        for v,lbl in fixed.items():
            gain[lbl//2]^=charges[v]
            if lbl&1:
                sw^=charges[v]
        initial=(tuple(gain),sw,(0,)*count,(0,)*count)
        layers=[{initial:None}]
        for v in remaining:
            layer={}
            for idx,lbl in enumerate(large):
                links=sum(1<<i for i,p in enumerate(cover) if zero(v,p,lbl,fixed[p]))
                for state in layers[-1]:
                    gains,switch,sizes,ports=state
                    gs,sz,pt=list(gains),list(sizes),list(ports)
                    gs[lbl//2]^=charges[v]
                    sz[idx]=min(cutoff+1,sz[idx]+1)
                    pt[idx]|=links
                    key=tuple(gs),switch^(charges[v] if lbl&1 else 0),tuple(sz),tuple(pt)
                    layer.setdefault(key,(state,lbl))
            layers.append(layer)
        for state in layers[-1]:
            gains,switch,sizes,ports=state
            u=zgain^switch
            if (any(sz!=cutoff+1 for sz in sizes) or any(g not in target for g in gains)
                    or u not in target or len(basis(gains)[1])!=h-1
                    or len(basis([*gains,u])[1])!=h):
                continue
            nodes=dict(fixed)
            nodes.update({n+j:lbl for j,lbl in enumerate(large)})
            links={v:set() for v in nodes}
            for a,b in combinations(fixed,2):
                if zero(a,b,fixed[a],fixed[b]):
                    links[a].add(b)
                    links[b].add(a)
            for j,mask in enumerate(ports):
                for i in bits(mask):
                    p=cover[i]
                    links[p].add(n+j)
                    links[n+j].add(p)
            connected=True
            for part in range(h):
                group={v for v,lbl in nodes.items() if lbl//2==part}
                if not group:
                    connected=False
                    break
                seen=set()
                todo=[next(iter(group))]
                while todo:
                    v=todo.pop()
                    if v not in seen:
                        seen.add(v)
                        todo.extend(links[v]-seen)
                if seen!=group:
                    connected=False
                    break
            if not connected:
                continue
            assign=dict(fixed)
            key=state
            for v,layer in zip(reversed(remaining),reversed(layers[1:])):
                key,assign[v]=layer[key]
            ids=[i for i,(a,b) in enumerate(edges) if not zero(a,b,assign[a],assign[b])]
            if trace(q,named,sum(1<<i for i in ids))!=target:
                raise ArithmeticError("original trace replay failed")
            return ids
        return None

    def choose_small(fixed,left,small,large):
        if not small:
            return test(fixed,left,large)
        lbl=small[0]
        for j in range(min(cutoff,len(left))+1):
            for subgroup in combinations(left,j):
                new=dict(fixed)
                new.update((v,lbl) for v in subgroup)
                remaining=tuple(v for v in left if v not in subgroup)
                ans=choose_small(new,remaining,small[1:],large)
                if ans is not None:
                    return ans
        return None

    for values in product(bins,repeat=len(cover)):
        fixed=dict(zip(cover,values))
        for k in range(min(len(bins),len(outside)//(cutoff+1))+1):
            for large in combinations(bins,k):
                small=tuple(b for b in bins if b not in large)
                ans=choose_small(fixed,outside,small,large)
                if ans is not None:
                    return ans
    return None


def check_small():
    """Cap the direct physical reference at nine edges; preserve shuffled IDs."""
    from random import Random
    from omega_signature_cover import signatures
    rng=Random(918)
    positive=negative=0
    for k in range(15):
        n=4+(k%2)
        edges=[e for e in combinations(range(n),2) if e!=(1,2) and not(k%3==0 and e==(0,3))]
        rng.shuffle(edges)
        cuts=[sum(1<<i for i,e in enumerate(edges) if v in e) for v in range(n)]
        # Start in a cover gauge, then scramble it, including on noncover edges.
        z=1<<next(i for i,e in enumerate(edges) if 0 in e)
        z^=combine(cuts,rng.randrange(1<<n))
        if len(basis(cuts+[z])[1])!=n:
            continue
        A=[rng.randrange(4) for _ in edges]
        D=cuts[1:]+[z]
        q=signatures(dependencies(signatures(D,len(edges))),len(edges))
        assert len(edges)<=9
        C={combine(cuts[1:],i) for i in range(1<<(n-1))}
        words=C|{z^c for c in C}
        attainable=set()
        for mask in range(1<<len(edges)):
            active=[w for w in words if not w&~mask]
            images=frozenset(combine(A,w) for w in active)
            if len(images)==len(active) and any(w not in C for w in active):
                attainable.add(images)
        for target in [{0},{0,1},{0,2},{0,3},{0,1,2,3}]:
            answer=solve(n,edges,q,z,A,[0],target)
            assert (answer is not None)==(frozenset(target) in attainable)
            if answer is None:
                negative+=1
            else:
                positive+=1
                s=sum(1<<i for i in answer)
                assert trace(q,A,s)==target and any(not w&~s for w in words-C)
    # Rank-four charge map fixes the normalized switch. All four outside
    # vertices must occupy one bin (strictly larger than 2d), and that bin
    # must connect to the fixed cover vertex despite the missing 12 edge.
    edges=[e for e in combinations(range(5),2) if e!=(1,2)]
    rng.shuffle(edges)
    cuts=[sum(1<<i for i,e in enumerate(edges) if v in e) for v in range(5)]
    z=1<<edges.index((0,1))
    D=cuts[1:]+[z]
    q=signatures(dependencies(signatures(D,len(edges))),len(edges))
    labels=[((1<<(b-1)) if a==0 else 0) | (16 if (a,b) in ((0,1),(0,3),(1,3)) else 0)
            for a,b in edges]
    answer=solve(5,edges,q,z,labels,[0],{0,17})
    assert answer==[edges.index((0,1))]
    assert positive and negative
    print("Bounded physical translated YES/NO:",positive,negative)


if __name__=="__main__":
    check_small()
