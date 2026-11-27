"""Discover exact local 2-CNF projections, eliminate them, and lift a SAT witness."""
from itertools import combinations, product
from operator import index

from private_projection_sat import binary_sat, literal_true, recognize_pairs


def solve_auto(clauses, *, private_limit=2, boundary_limit=2):
    """Return sat/unsat, or unknown when bounded verified reductions stall."""
    p, b = map(index, (private_limit, boundary_limit))
    if min(p,b)<0:
        raise ValueError("negative discovery bound")
    original=[tuple(dict.fromkeys(row)) for row in clauses]
    if any(type(x) is not int or not x for row in original for x in row):
        raise ValueError("expected signed nonzero integers")
    rows={row for row in original if not any(-x in row for x in row)}
    stats={'candidates':0,'local_words':0,'eliminations':0,'binary_calls':0}
    stack=[]
    # Preserve known disjoint gadgets even when another sound local reduction
    # could leave a different residual outside the bounded search.
    priority=iter(recognize_pairs(sorted(rows)) if p>=2 else ())

    def project(block):
        private=set(block)
        touching=[row for row in rows if any(abs(x) in private for x in row)]
        if not any(len(row)>2 for row in touching):
            return None
        connected = {block[0]}
        for _ in block:
            for row in touching:
                local = {abs(x) for x in row} & private
                if connected & local:
                    connected.update(local)
        if connected != private:
            return None
        boundary=sorted({abs(x) for row in touching for x in row}-private)
        if len(boundary)>b:
            return None
        extensions={}
        for outer in product((False,True),repeat=len(boundary)):
            assignment=dict(zip(boundary,outer))
            for inner in product((False,True),repeat=len(block)):
                stats['local_words']+=1
                assignment.update(zip(block,inner))
                if all(any(literal_true(x,assignment) for x in row) for row in touching):
                    extensions[outer]=inner
                    break
        if not extensions:
            return touching,[()],boundary,extensions
        binary=[]
        for k in (1,2):
            for ids in combinations(range(len(boundary)),k):
                present={tuple(word[i] for i in ids) for word in extensions}
                for pat in product((False,True),repeat=k):
                    if pat not in present:
                        binary.append(tuple(-boundary[i] if val else boundary[i]
                                            for i,val in zip(ids,pat)))
        # Verify every projected row, including absent tuples at arity >2.
        for outer in product((False,True),repeat=len(boundary)):
            if outer not in extensions:
                a=dict(zip(boundary,outer))
                if all(any(literal_true(x,a) for x in row) for row in binary):
                    return None
        return touching,binary,boundary,extensions

    while () not in rows and any(len(row)>2 for row in rows):
        appearing=sorted({abs(x) for row in rows for x in row})
        def trials():
            yield from priority
            for k in range(1,min(p,len(appearing))+1):
                yield from combinations(appearing,k)
        for block in trials():
            stats['candidates']+=1
            proposal=project(block)
            if proposal is None:
                continue
            touching,binary,boundary,extensions=proposal
            rows.difference_update(touching)
            rows.update(binary)
            stack.append((block,boundary,extensions))
            stats['eliminations']+=1
            break
        else:
            return dict(status='unknown',stats=stats)
    stats['binary_calls']+=1
    if not binary_sat(rows):
        return dict(status='unsat',stats=stats)
    pins=[]
    assignment={}
    for v in sorted({abs(x) for row in rows for x in row}):
        stats['binary_calls']+=1
        positive=binary_sat([*rows,*pins,(v,)])
        assignment[v]=positive
        pins.append((v if positive else -v,))
    for block,boundary,extensions in reversed(stack):
        outer=tuple(assignment.setdefault(x,False) for x in boundary)
        assignment.update(zip(block,extensions[outer]))
    for row in original:
        for x in row:
            assignment.setdefault(abs(x),False)
    if not all(any(literal_true(x,assignment) for x in row) for row in original):
        raise ArithmeticError("lifted witness failed")
    return dict(status='sat',witness=assignment,stats=stats)
