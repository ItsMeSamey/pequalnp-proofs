"""Deterministic generator isolation for signed 2-CNF and XOR."""
from itertools import combinations
from affine_projective_layer import _two_sat
from horn_closure_xor import _rules, _closure, _rows
from bijunctive_xor_hull import add_vector, reduce_vector, image


def red_sets(N,k,budget):
    width=(max(1,N)-1).bit_length()
    for d in range(min(max(0,budget-1),width)+1):
        for positions in combinations(range(width),d):
            mask=sum(1<<j for j in positions)
            buckets={}
            for v in range(N):
                key=v&mask
                buckets[key]=buckets.get(key,0)|(1<<v)
            for j in range(min(k,len(buckets))+1):
                for chosen in combinations(buckets.values(),j):
                    yield sum(chosen)


def prepare(n,clauses,parity):
    if not isinstance(n,int) or n<0:raise ValueError("invalid dimension")
    clauses=[tuple(dict.fromkeys(c)) for c in clauses]
    if any(len(c)>2 or any(not isinstance(l,int) or not 1<=abs(l)<=n for l in c) for c in clauses):
        raise ValueError("expected a signed binary formula")
    rows=_rows(n,parity)
    if rows is None or any(not c for c in clauses):return None
    base=0
    if not all(any(l<0 for l in c) for c in clauses):
        binary=[tuple(2*(abs(l)-1)+(l>0) for l in (c[0],c[-1])) for c in clauses]
        model=_two_sat(n,binary)
        if model is None:return None
        base=sum(1<<j for j,b in enumerate(model) if b)
    rules=_rules(n,[[(-l if base>>(abs(l)-1)&1 else l) for l in c] for c in clauses])
    labels=tuple(sum(((m>>i)&1)<<j for j,(m,_) in enumerate(rows)) for i in range(n))
    target=sum(b<<j for j,(_,b) in enumerate(rows))^image(base,labels)
    classes={}
    for v in range(n):
        p=_closure(rules,1<<v)
        if p is not None:classes[p]=classes.get(p,0)|(1<<v)
    closures=tuple(classes)
    active=sum((members&-members) for members in classes.values() if image(members,labels))
    bad=[b for b,h in rules if not h]
    conflicts=tuple((i,j) for j,a in enumerate(closures) for i in range(j)
                    if any((closures[i]|a)&b==b for b in bad))
    return dict(baseline=base,closures=closures,conflicts=conflicts,labels=labels,target=target,
                rank=len(rows),active_markers=active)


def solve(n,clauses,parity):
    clauses=tuple(tuple(c) for c in clauses); parity=tuple(parity)
    data=prepare(n,clauses,parity)
    stats={"colourings":0,"generators":0,"max_degree":0}
    if data is None:return None,stats
    P=data['closures']; N=len(P); k=data['rank']; target=data['target']
    labels=data['labels']; base=data['baseline']
    if not target:return base,stats
    conflicts=[0]*N; adj=[0]*N
    for i,j in data['conflicts']:
        conflicts[i]|=1<<j; conflicts[j]|=1<<i
    for j,a in enumerate(P):
        for i in range(j):
            if conflicts[i]>>j&1 or a&P[i]&data['active_markers']:
                adj[i]|=1<<j; adj[j]|=1<<i
    degree=max((m.bit_count() for m in adj),default=0)
    K=min(N,k*(degree+1))
    stats.update(generators=N,max_degree=degree,rank=k,isolation_budget=K)
    for red in red_sets(N,k,K):
        stats["colourings"]+=1
        available={}; components=[]
        while red:
            frontier=red&-red; red^=frontier
            union=0; members=0; forbidden=0
            while frontier:
                bit=frontier&-frontier; frontier^=bit; v=bit.bit_length()-1
                members|=bit; union|=P[v]; forbidden|=conflicts[v]
                added=adj[v]&red
                frontier|=added;red^=added
            if not members&forbidden:
                add_vector(image(union,labels),1<<len(components),available)
                components.append(union)
        residual,tag=reduce_vector(target,available)
        if not residual:
            toggle=0
            for i,union in enumerate(components):
                if tag>>i&1:toggle|=union
            word=base^toggle
            assert all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
            assert all((word&m).bit_count()%2==b for m,b in parity)
            return word,stats
    return None,stats
