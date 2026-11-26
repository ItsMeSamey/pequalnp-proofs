"""Exact SAT+XOR by vertex cover of the weighted closure-generator interactions."""
from itertools import combinations
from bijunctive_xor_hull import add_vector,reduce_vector
from two_sat_generator_interaction import prepare


def minimum_cover(edges):
    """An exact minimum vertex cover by iterative-deepening endpoint branching."""
    edges=tuple(edges)
    for budget in range(len(edges)+1):
        todo=[(0,budget)]
        while todo:
            chosen,left=todo.pop()
            missing=next(((u,v) for u,v in edges if not chosen & ((1<<u)|(1<<v))),None)
            if missing is None:
                return chosen
            if left:
                u,v=missing
                todo.extend(((chosen|1<<u,left-1),(chosen|1<<v,left-1)))
    raise AssertionError("unreachable")


def interactions(closures,labels,conflicts):
    """Return aggregated (support mask -> syndrome) and all graph edges."""
    grouped={}
    raw=0
    for i,label in enumerate(labels):
        if label:
            support=sum((1<<j) for j,p in enumerate(closures) if p>>i&1)
            if support:
                raw+=1
                grouped[support]=grouped.get(support,0)^label
    signatures={s:v for s,v in grouped.items() if v}
    edges=set(conflicts)
    for support in signatures:
        members=[j for j in range(len(closures)) if support>>j&1]
        edges.update(combinations(members,2))
    return signatures,tuple(sorted(edges)),raw,len(grouped)-len(signatures)


def solve(n,clauses,xor_rows):
    """Return (original witness or None, structural metrics). Clauses have width ≤2."""
    clauses=tuple(tuple(c) for c in clauses)
    rows=tuple(xor_rows)
    data=prepare(n,clauses,rows)
    if data is None:
        return None,{"preprocessing_conflict":True}
    closures=data["closures"]
    signatures,edges,raw,cancelled=interactions(closures,data["labels"],data["conflicts"])
    cover=minimum_cover(edges)
    C=[i for i in range(len(closures)) if cover>>i&1]
    allmask=(1<<len(closures))-1
    stats=dict(xor_rank=data["rank"],generators=len(closures),raw_nonzero_toggles=raw,
               nonzero_signatures=len(signatures),cancelled_signatures=cancelled,
               interaction_edges=len(edges),cover_size=len(C),pin_branches=0)
    for pin in range(1<<len(C)):
        stats["pin_branches"]+=1
        selected=sum(1<<i for j,i in enumerate(C) if pin>>j&1)
        available=allmask^cover
        for i,j in data["conflicts"]:
            if selected>>i&selected>>j&1:
                break
            if selected>>i&1:
                available &= ~(1<<j)
            if selected>>j&1:
                available &= ~(1<<i)
        else:
            rhs=data["target"]
            columns={}
            for mask,weight in signatures.items():
                if mask & selected:
                    rhs^=weight
                else:
                    survivor=mask&available
                    if survivor:
                        assert not survivor & (survivor-1)
                        columns[survivor]=columns.get(survivor,0)^weight
            basis={}
            for bit,label in columns.items():
                add_vector(label,bit,basis)
            remainder,tag=reduce_vector(rhs,basis)
            if not remainder:
                toggles=0
                for i,c in enumerate(closures):
                    if (tag|selected)>>i&1:
                        toggles|=c
                word=data["baseline"]^toggles
                assert all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
                assert all((word&a).bit_count()%2==b for a,b in rows)
                return word,stats
    return None,stats
