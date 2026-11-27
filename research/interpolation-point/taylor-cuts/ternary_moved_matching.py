"""Exact bounded-support search for a GF(3)-labelled perfect matching."""
from functools import lru_cache
from itertools import combinations


def solve(n, edges, base, target, *, left=None, cap=None):
    """n counts vertices, base and the returned witness use original edge indices."""
    if type(n) is not int or n<0 or n%2 or (cap is not None and (type(cap) is not int or cap<0)):
        raise ValueError('invalid order or support cap')
    edges = [(u,v,tuple(g)) for u,v,g in edges]
    base, target = tuple(base), tuple(target)
    b = len(target)
    if any(x not in (0,1,2) for x in target):
        raise ValueError('invalid target')
    adj = [[] for _ in range(n)]
    neighbors = [set() for _ in range(n)]
    left = None if left is None else frozenset(left)
    if left is not None and (not left<=set(range(n)) or len(left)!=n//2):
        raise ValueError('invalid bipartition')
    for i,(u,v,g) in enumerate(edges):
        if not (0<=u<n and 0<=v<n and u!=v and len(g)==b and all(x in (0,1,2) for x in g)):
            raise ValueError('invalid labelled edge')
        if left is not None and ((u in left)==(v in left)):
            raise ValueError('edge inside a side')
        adj[u].append((v,i))
        adj[v].append((u,i))
        neighbors[u].add(v)
        neighbors[v].add(u)
    if any(i<0 or i>=len(edges) for i in base) or sorted(v for i in base for v in edges[i][:2])!=list(range(n)):
        raise ValueError('invalid base matching')
    degree = n-1 if left is None else n//2
    delta = max((degree-len(nb) for nb in neighbors),default=0)
    bound = min(n//2,2*b*(2*delta+5))
    limit = bound if cap is None else min(bound,cap)
    def label(ids):
        return tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(b))
    def minus(x,y):
        return tuple((a-b)%3 for a,b in zip(x,y))
    zero = (0,)*b
    total = label(base)
    stats = dict(delta=delta,bound=bound,limit=limit,subsets=0,states=0)
    base_set = set(base)
    for size in range(limit+1):
        for moved in combinations(base,size):
            stats['subsets']+=1
            mask = sum(1<<v for i in moved for v in edges[i][:2])
            need = minus(target,minus(total,label(moved)))
            @lru_cache(maxsize=None)
            def local(mask, residual):
                if not mask:
                    return () if residual==zero else None
                bit = mask & -mask
                u = bit.bit_length()-1
                for v,i in adj[u]:
                    if i in base_set or not (mask>>v & 1):
                        continue
                    tail = local(mask^bit^(1<<v),minus(residual,edges[i][2]))
                    if tail is not None:
                        return (i,)+tail
                return None
            replacement = local(mask,need)
            stats['states']+=local.cache_info().currsize
            local.cache_clear()
            if replacement is not None:
                witness=tuple(sorted((base_set-set(moved))|set(replacement)))
                if sorted(v for i in witness for v in edges[i][:2])!=list(range(n)) or label(witness)!=target:
                    raise ArithmeticError('invalid witness')
                return 'SAT',witness,stats
    return ('UNSAT' if limit==bound else 'UNKNOWN'),None,stats
