"""Exact counting with inclusion-exclusion over omitted affine cylinders."""
from affine_relation import affine_hull
from event_affine_factors import _omissions


def _insert(basis, mask, rhs):
    while mask:
        pivot = mask.bit_length()-1
        if pivot not in basis:
            basis[pivot] = mask, rhs
            return True
        row, value = basis[pivot]
        mask ^= row
        rhs ^= value
    return not rhs


def _word(basis):
    word = 0
    for pivot in sorted(basis):
        row, value = basis[pivot]
        if (row & word).bit_count() % 2 != value:
            word |= 1 << pivot
    return word


def solve(domains,constraints,output,*,codebooks=None,omission_cap=None,branch_cap=None):
    """branch_cap covers all subset terms for counts and witness recovery."""
    for cap in (omission_cap,branch_cap):
        if cap is not None and (type(cap) is not int or cap<0):
            raise ValueError("invalid affine budgets")
    domains={v:tuple(D) for v,D in domains.items()}
    if output not in domains or any(type(bit) not in (int,bool) or bit not in (0,1) for bit in domains[output]):
        raise ValueError("invalid terminal bit domain")
    custom={} if codebooks is None else dict(codebooks)
    if custom.keys()-domains.keys():
        raise ValueError("codebook for unknown variable")
    enc,dec,width,offset={},{},{},{}
    total=0
    for v,D in domains.items():
        if len(set(D))!=len(D):
            raise ValueError("duplicate domain record")
        book=dict(custom[v]) if v in custom else {x:i for i,x in enumerate(D)}
        if (not set(D)<=book.keys() or any(type(a) is not int or a<0 for a in book.values())
                or len(set(book.values()))!=len(book)):
            raise ValueError("incomplete or noninjective integer codebook")
        enc[v]={x:book[x] for x in D}
        dec[v]={a:x for x,a in enc[v].items()}
        width[v]=max((a.bit_length() for a in book.values()),default=0)
        offset[v]=total
        total+=width[v]
    factors=[((v,),set(dec[v])) for v in domains]
    relations=[]
    for u,v,allowed in constraints:
        if u not in domains or v not in domains:
            raise ValueError("constraint on unknown variable")
        pairs=frozenset((x,y) for x,y in allowed if x in enc[u] and y in enc[v])
        relations.append((u,v,pairs))
        if u==v:
            factors.append(((u,),{enc[u][x] for x,y in pairs if x==y}))
        else:
            factors.append(((u,v),{enc[u][x]|(enc[v][y]<<width[u]) for x,y in pairs}))
    metrics=dict(bits=total,factors=len(factors),exception_count=0,nonaffine_factors=0,
                 equations=0,branches=0,branch_states=0,codebook_entries=sum(map(len,enc.values())))
    metrics.update(cylinders=0,count_calls=0,subset_terms=0)
    counts = {0:0, 1:0}
    witnesses={}
    def result(status,reason=None):
        out=dict(status=status,witnesses=witnesses,metrics=metrics)
        if reason:
            out["reason"]=reason
        if status != "unknown":
            out["counts"] = dict(counts)
        if status=="constant":
            out["value"]=next(iter(witnesses))
        return out
    if any(not points for scope,points in factors):
        return result("empty")
    equations=[]
    forbidden=[]
    pending=[]
    for scope,points in factors:
        size=sum(width[v] for v in scope)
        eq,dim=affine_hull(points,size)
        holes=(1<<dim)-len(points)
        metrics["exception_count"]+=holes
        metrics["nonaffine_factors"]+=int(bool(holes))
        def scatter(word):
            packed=0
            for v in scope:
                packed|=(word&((1<<width[v])-1))<<offset[v]
                word>>=width[v]
            return packed
        equations.extend((scatter(m),b) for m,b in eq)
        if holes:
            pending.append((scope,points))
    metrics["equations"]=len(equations)
    if omission_cap is not None and metrics["exception_count"] > omission_cap:
        return result("unknown","omission cap")
    for scope,points in pending:
        positions=[offset[v]+j for v in scope for j in range(width[v])]
        mask=sum(1<<p for p in positions)
        for hole in _omissions(points):
            target=sum(((hole>>j)&1)<<p for j,p in enumerate(positions))
            forbidden.append((mask,target))

    base = {}
    for mask, rhs in equations:
        if not _insert(base, mask, rhs):
            return result('empty')
    cylinders = sorted(set(forbidden))
    metrics['cylinders'] = len(cylinders)
    terms = 1 << len(cylinders)

    def count(pin, value):
        if branch_cap is not None and terms > branch_cap - metrics['subset_terms']:
            return None, None
        metrics['count_calls'] += 1
        accumulator = 0
        candidate = None
        for subset in range(terms):
            metrics['subset_terms'] += 1
            metrics['branch_states'] += 1
            mask, target = pin, value
            remaining = subset
            while remaining:
                bit = remaining & -remaining
                extra, wanted = cylinders[bit.bit_length() - 1]
                if (target ^ wanted) & mask & extra:
                    break
                mask |= extra
                target |= wanted
                remaining ^= bit
            else:
                rows = base.copy()
                while mask:
                    bit = mask & -mask
                    if not _insert(rows, bit, int(bool(target & bit))):
                        break
                    mask ^= bit
                else:
                    weight = 1 << (total - len(rows))
                    accumulator += -weight if subset.bit_count() & 1 else weight
                    if subset == 0:
                        candidate = _word(rows)
        return accumulator, candidate

    for bit in (0, 1):
        if bit not in enc[output]:
            continue
        pin = ((1 << width[output]) - 1) << offset[output]
        value = enc[output][bit] << offset[output]
        number, word = count(pin, value)
        if number is None:
            return result('unknown', 'branch cap')
        counts[bit] = number
        if not number:
            continue
        if number < 0 or word is None:
            raise ArithmeticError('invalid affine cylinder count')
        for j in range(total):
            if all(word & m != t for m, t in cylinders):
                break
            coord = 1 << j
            if pin & coord:
                continue
            pin |= coord
            zero, candidate = count(pin, value)
            if zero is None:
                return result('unknown', 'branch cap')
            if zero:
                word = candidate
            else:
                value |= coord
        else:
            # All coordinates have been pinned to a positive-count branch.
            word = value
        witness = {v:dec[v][(word >> offset[v]) & ((1 << width[v]) - 1)] for v in domains}
        if witness[output] != bit or any((witness[u],witness[v]) not in pairs for u,v,pairs in relations):
            raise ArithmeticError('decoded assignment failed original factors')
        witnesses[bit] = witness
    return result(('empty','constant','pair')[len(witnesses)])
