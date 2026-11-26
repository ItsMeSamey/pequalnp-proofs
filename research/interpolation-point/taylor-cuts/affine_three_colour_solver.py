"""Decode rank-two affine flats to ternary matching constraints and count."""
from collections import Counter, defaultdict

from affine_cover_solver import insert


def _witness(basis):
    value = 0
    for pivot in sorted(basis):
        mask, rhs = basis[pivot]
        value |= (rhs ^ ((mask & value).bit_count() % 2)) << pivot
    return value


def decode(n, flats):
    """Return local normal pairs, domains and edge matchings, or None."""
    if not isinstance(n,int) or n < 0:
        raise ValueError("invalid dimension")
    profiles = defaultdict(set)
    for flat in flats:
        basis = {}
        consistent = True
        for mask,rhs in flat:
            if not isinstance(mask,int) or mask < 0 or mask.bit_length()>n or rhs not in (0,1):
                raise ValueError("invalid equation")
            consistent &= insert(mask,rhs,basis)
        if not consistent or len(basis)!=2:
            return None
        (a,i),(b,j) = basis.values()
        signed = {a:i,b:j,a^b:i^j}
        plane = tuple(sorted(signed))
        profiles[plane].add(tuple(signed[x] for x in plane))
    freq = Counter(x for plane in profiles for x in plane)
    planes, edges = [], []
    for plane in sorted(profiles):
        shared = [x for x in plane if freq[x]>1]
        if len(shared) in (0,3):
            planes.append(plane)
        elif len(shared)==2:
            edges.append((plane,shared))
        else:
            return None
    owners, basis, pairs, domains = {}, {}, [], []
    for i,plane in enumerate(planes):
        p,q,_ = plane
        before = len(basis)
        for v in (p,q):
            insert(v,0,basis)
        if len(basis)!=before+2 or len(profiles[plane])!=1:
            return None
        a,b,_ = next(iter(profiles[plane]))
        pairs.append((p,q))
        domains.append(tuple(x for x in range(4) if x != a+2*b))
        for mask,coef in zip(plane,(1,2,3)):
            owners[mask] = (i,coef)
    rules = defaultdict(set)
    for plane,(p,q) in edges:
        if p not in owners or q not in owners:
            return None
        u,k = owners[p]
        v,l = owners[q]
        if u==v:
            return None
        for values in profiles[plane]:
            a,b = values[plane.index(p)],values[plane.index(q)]
            left = [x for x in domains[u] if (x&k).bit_count()%2==a]
            right = [x for x in domains[v] if (x&l).bit_count()%2==b]
            if len(left)!=1 or len(right)!=1:
                return None
            if u<v:
                rules[u,v].add((left[0],right[0]))
            else:
                rules[v,u].add((right[0],left[0]))
    for rule in rules.values():
        if len(rule)!=3 or any(len({pair[t] for pair in rule})!=3 for t in (0,1)):
            return None
    return pairs,domains,{edge:dict(rule) for edge,rule in rules.items()}


def _synchronize(domains,rules):
    graph = [[] for _ in domains]
    for (i,j),perm in rules.items():
        graph[i].append((j,perm))
        graph[j].append((i,{b:a for a,b in perm.items()}))
    chosen = {}
    for root,domain in enumerate(domains):
        if root in chosen:
            continue
        for color in domain:
            trial = {root:color}
            stack = [root]
            valid = True
            while stack and valid:
                u = stack.pop()
                for v,perm in graph[u]:
                    target = perm[trial[u]]
                    if v in trial:
                        if trial[v]!=target:
                            valid = False
                            break
                    else:
                        trial[v] = target
                        stack.append(v)
            if valid:
                chosen.update(trial)
                break
        else:
            return None
    return [chosen[i] for i in range(len(domains))]


def count_three_colour(n,flats):
    """Return (count, original witness) or None on structural/gauge rejection."""
    decoded = decode(n,flats)
    if decoded is None:
        return None
    pairs,domains,rules = decoded
    stars = _synchronize(domains,rules)
    if stars is None:
        return None
    size = len(domains)
    residual = [[c for c in d if c != star] for d,star in zip(domains,stars)]
    count,witness = 0,None
    for subset in range(1<<size):
        basis = {}
        for (i,j),perm in rules.items():
            a,b = subset>>i&1,subset>>j&1
            if a and b:
                break
            if not a and not b:
                conflict = residual[j].index(perm[residual[i][0]])
                if not insert((1<<i)|(1<<j),conflict^1,basis):
                    break
        else:
            count += 1 << (n-2*size+size-subset.bit_count()-len(basis))
            if witness is None:
                bits = _witness(basis)
                eqs = {}
                for i,(p,q) in enumerate(pairs):
                    color = stars[i] if subset>>i&1 else residual[i][bits>>i&1]
                    insert(p,color&1,eqs)
                    insert(q,color>>1,eqs)
                witness = _witness(eqs)
    return count,witness
