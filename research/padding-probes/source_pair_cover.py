"""Minimum unsigned pair cover of residual ternary variable scopes."""
from itertools import combinations


def solve_scopes(scopes,*,node_cap=None):
    if node_cap is not None and (type(node_cap) is not int or node_cap<0):
        raise ValueError("invalid node cap")
    distinct = set()
    for scope in scopes:
        row = tuple(scope)
        if len(row)!=3 or any(type(j) is not int or j<1 for j in row) or len(set(row))!=3:
            raise ValueError("three distinct positive labels required")
        distinct.add(tuple(sorted(row)))
    choices = [tuple(combinations(row,2)) for row in sorted(distinct)]
    incident = {}
    for i,pairs in enumerate(choices):
        for pair in pairs:
            incident[pair] = incident.get(pair,0) | (1<<i)
    full = (1<<len(choices))-1
    stats = dict(scopes=len(choices),pairs=len(incident),nodes=0,limits_started=0,
                 greedy_pair_scores=0,packing_checks=0,children_generated=0,forced_pairs=0,kernel_prunes=0,degree_checks=0)
    mask = full
    greedy = []
    while mask:
        stats["greedy_pair_scores"] += len(incident)
        pair = min(incident,key=lambda p:(-(incident[p]&mask).bit_count(),p))
        greedy.append(pair)
        mask &= ~incident[pair]
    best = tuple(sorted(greedy))
    used = set()
    lower = 0
    for pairs in choices:
        stats["packing_checks"] += 1
        if used.isdisjoint(pairs):
            lower += 1
            used.update(pairs)
    def answer(status,low,cover):
        return dict(status=status,cover=cover,lower_bound=low,upper_bound=len(cover),metrics=stats)
    for limit in range(lower,len(best)):
        stats["limits_started"] += 1
        stack = [(full,())]
        while stack:
            if node_cap is not None and stats["nodes"]>=node_cap:
                return answer("cutoff",limit,best)
            mask,path = stack.pop()
            stats["nodes"] += 1
            while mask and len(path)<limit:
                budget = limit-len(path)
                forced = None
                for pair,neighbors in incident.items():
                    stats["degree_checks"] += 1
                    if (mask&neighbors).bit_count()>budget:
                        forced = pair
                        break
                if forced is None:
                    break
                path += (forced,)
                mask &= ~incident[forced]
                stats["forced_pairs"] += 1
            if not mask:
                return answer("optimal",len(path),tuple(sorted(path)))
            if len(path)==limit:
                continue
            if mask.bit_count()>(limit-len(path))**2:
                stats["kernel_prunes"] += 1
                continue
            first = (mask&-mask).bit_length()-1
            for pair in reversed(choices[first]):
                stack.append((mask & ~incident[pair],path+(pair,)))
                stats["children_generated"] += 1
    return answer("optimal",len(best),best)


def solve(n,clauses,*,pins=(),node_cap=None):
    if type(n) is not int or n<0:
        raise ValueError("invalid declared arity")
    fixed = {}
    conflict = False
    for j,bit in pins.items() if hasattr(pins,"items") else pins:
        if type(j) is not int or not 1<=j<=n or type(bit) not in (bool,int) or bit not in (0,1):
            raise ValueError("invalid pin")
        conflict |= j in fixed and fixed[j]!=bit
        fixed[j] = int(bit)
    scopes = []
    visits = 0
    for clause in clauses:
        row = tuple(clause)
        visits += len(row)
        if any(type(x) is not int or not 1<=abs(x)<=n for x in row):
            raise ValueError("invalid source literal")
        literals = set(row)
        if any(-x in literals or fixed.get(abs(x))==int(x>0) for x in literals):
            continue
        live = {abs(x) for x in literals if abs(x) not in fixed}
        if len(live)>3:
            raise ValueError("residual clause width exceeds three")
        if not live:
            conflict = True
        if len(live)==3:
            scopes.append(live)
    result = solve_scopes(scopes,node_cap=node_cap)
    result["source_conflict"] = conflict
    result["metrics"]["source_literal_visits"] = visits
    return result
