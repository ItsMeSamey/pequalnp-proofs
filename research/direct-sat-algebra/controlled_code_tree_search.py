"""Capped planning for positive code-block evaluation; no counting during planning.

clock_cap counts the exponential table-entry/character units of controlled_code_blocks,
not Python operations. The polynomial bit-operation and witness overhead is additional.
An independent planning_cap bounds the number of greedy/exact planner work units
(subset states plus candidate merges). An uncertified run returns UNKNOWN.
"""
from dataclasses import dataclass
from controlled_code_blocks import balanced, solve
from controlled_witness_radius import column_basis
from quadratic_target import reduce_vector


@dataclass
class Result:
    status: str
    count: object
    witness: object
    tree: object
    clock: object
    strategy: str
    optimal: bool
    planning_units: int


def plan_and_solve(m, A, b, U, activators, *, clock_cap, exact_limit=12,
                   planning_cap=1_000_000, decision_only=False):
    A,U,activators=tuple(A),tuple(U),tuple(activators)
    k,n=len(U),len(A)
    if min(m,clock_cap,exact_limit,planning_cap)<0 or len(activators)!=k:
        raise ValueError("invalid dimensions or cap")
    if any(not 0<=v<1<<m for v in (*A,b,*U)):
        raise ValueError("output column exceeds dimension")
    if any(not 0<=v<1<<n or c not in (0,1) for v,c in activators):
        raise ValueError("invalid activator")
    data=[(A[j]<<k) | sum(((v>>j)&1)<<i for i,(v,_) in enumerate(activators))
          for j in range(n)]
    basis=column_basis(data)

    def residue(v):
        return reduce_vector(v,basis)[0]

    a=[residue(1<<i) for i in range(k)]
    d=[residue(u<<k) for u in U]
    h=residue((b<<k) | sum(c<<i for i,(_,c) in enumerate(activators)))
    all_basis=column_basis(a+d)
    if reduce_vector(h,all_basis)[0]:
        return Result("UNSAT",False if decision_only else 0,None,None,0,"linear",True,0)
    if not k:
        value,witness,_=solve(m,A,b,U,activators,decision_only=decision_only)
        return Result("SAT",value,witness,None,0,"empty",True,0)

    full=(1<<k)-1
    rank_cache={0:0,full:len(all_basis)}
    def inside_rank(s):
        if s not in rank_cache:
            rank_cache[s]=len(column_basis(v for i in range(k) if s>>i&1 for v in (a[i],d[i])))
        return rank_cache[s]

    def width(s):
        return inside_rank(s)+inside_rank(full^s)-len(all_basis)

    info={}
    def terminal(s):
        if s not in info:
            D=len(column_basis(d[i] for i in range(k) if s>>i&1))
            info[s]=1<<(width(s)+D)
        return info[s]

    # A root terminal needs no interface table. Its descendants in the supplied
    # candidate tree are planned only by polynomial-rank calculations.
    root_cost=4 if k==1 else terminal(full)
    best_cost=root_cost
    best_tree=balanced(range(k))
    strategy="root bound"
    optimal=(k==1)
    units=0
    subsets=(1<<k)-1
    exact_units=None
    if k<=exact_limit and subsets<=planning_cap:
        exact_units=subsets+(3**k-2**(k+1)+1)//2
    if exact_units is not None and exact_units<=planning_cap:
        costs={}
        split={}
        for s in range(1,full+1):
            if s&(s-1)==0:
                costs[s]=4
                continue
            costs[s]=terminal(s)
            # Anchor lsb in the right child, so each unordered split appears once.
            movable=s^(s&-s)
            left=movable
            while left:
                right=s^left
                cost=costs[left]+costs[right]+(1<<(width(left)+width(right)))
                if cost<costs[s]:
                    costs[s]=cost
                    split[s]=(left,right)
                left=(left-1)&movable

        def reconstruct(s):
            if s in split:
                left,right=split[s]
                return reconstruct(left),reconstruct(right)
            return balanced([i for i in range(k) if s>>i&1])

        best_cost,best_tree=costs[full],reconstruct(full)
        strategy,optimal,units="exact",True,exact_units
    else:
        greedy_units=k+k*(k-1)*(k+1)//6
        if greedy_units<=planning_cap:
            blocks={1<<i:(4,i) for i in range(k)}
            while len(blocks)>1:
                masks=sorted(blocks)
                choice=None
                for pos,left in enumerate(masks):
                    for right in masks[pos+1:]:
                        s=left|right
                        cost=min(terminal(s),blocks[left][0]+blocks[right][0]+
                                 (1<<(width(left)+width(right))))
                        key=(width(s),cost,left,right)
                        if choice is None or key<choice:
                            choice=key
                _,cost,left,right=choice
                ltree=blocks.pop(left)[1]
                rtree=blocks.pop(right)[1]
                blocks[left|right]=cost,(ltree,rtree)
            best_cost,best_tree=blocks[full]
            strategy,units="greedy",greedy_units
    if best_cost>clock_cap:
        return Result("UNKNOWN",None,None,best_tree,best_cost,strategy,optimal,units)
    value,witness,stats=solve(m,A,b,U,activators,best_tree,decision_only=decision_only)
    actual=stats["clock"]
    if actual>best_cost:
        raise AssertionError("planner underestimated certified work")
    return Result("SAT" if witness is not None else "UNSAT",value,witness,
                  best_tree,actual,strategy,optimal,units)
