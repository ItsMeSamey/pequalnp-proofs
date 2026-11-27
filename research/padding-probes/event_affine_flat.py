"""Project Gaussian cylinders to affine flats and solve in the active dual span."""
from event_affine_compile import compile_factors
from orbit_rado import reduce_row, insert


def prepare(width, equations, cylinders):
    """Preserve the entire solution set under unit and parallel-plane propagation."""
    if type(width) is not int or width < 0:
        raise ValueError('nonnegative width required')
    equations, cylinders = tuple(equations), tuple(cylinders)
    def valid(mask):
        return type(mask) is int and mask >= 0 and mask.bit_length() <= width
    if any(not valid(m) or type(b) not in (bool,int) or b not in (0,1) for m,b in equations):
        raise ValueError('invalid equation')
    if any(not valid(m) or not valid(t) or t & ~m for m,t in cylinders):
        raise ValueError('invalid cylinder')
    metrics = dict(propagated=0,parallel_groups=0,dropped=0,projected_dimension=0,
                   residual_rank=0,cover_calls=0)
    impossible = dict(status='unsat',metrics=metrics)
    seed = {}
    for mask,rhs in equations:
        if not insert(seed,mask,rhs):
            return impossible
    active = []
    for mask,target in cylinders:
        rows = []
        while mask:
            bit = mask & -mask
            rows.append((bit,int(bool(bit & target))))
            mask ^= bit
        active.append(rows)
    while True:
        remaining, units, planes = [], [], {}
        for flat in active:
            local = {}
            for mask,rhs in flat:
                mask,rhs = reduce_row(seed,mask,rhs)
                if not insert(local,mask,rhs):
                    metrics['dropped'] += 1
                    break
            else:
                if not local:
                    return impossible
                if len(local) == 1:
                    mask,rhs = next(iter(local.values()))
                    units.append((mask,rhs ^ 1))
                elif len(local) == 2:
                    lo,hi = sorted(local)
                    a,x = local[lo]
                    b,y = local[hi]
                    if (b >> lo) & 1:
                        b,y = b ^ a,y ^ x
                    planes.setdefault((a,b),set()).add(x | (y << 1))
                else:
                    remaining.append(tuple(local.values()))
        for (a,b),bad in planes.items():
            if len(bad) == 1:
                v = next(iter(bad))
                remaining.append(((a,v & 1),(b,v >> 1)))
                continue
            metrics['parallel_groups'] += 1
            allowed = set(range(4)) - bad
            if not allowed:
                return impossible
            for direction, mask in ((1,a),(2,b),(3,a ^ b)):
                values = {(direction & v).bit_count() % 2 for v in allowed}
                if len(values) == 1:
                    units.append((mask,values.pop()))
        active = remaining
        if not units:
            break
        rank = len(seed)
        for mask,rhs in units:
            if not insert(seed,mask,rhs):
                return impossible
        metrics['propagated'] += len(seed)-rank
        if len(seed) == rank:
            raise ArithmeticError('non-shrinking propagation')
    normals,coordinates = {}, []
    for flat in active:
        for mask,_ in flat:
            rest,_ = reduce_row(normals,mask)
            if rest:
                normals[rest.bit_length()-1] = rest,1 << len(coordinates)
                coordinates.append(rest)
    flats = []
    for flat in active:
        packed = []
        for mask,rhs in flat:
            rest,combination = reduce_row(normals,mask)
            if rest:
                raise ArithmeticError('coordinate extraction failed')
            packed.append((combination,rhs))
        flats.append(tuple(packed))
    dimension = len(coordinates)
    metrics.update(projected_dimension=dimension,residual_rank=max(map(len,flats),default=0))
    return dict(status='ok',seed=seed,coordinates=coordinates,flats=flats,dimension=dimension,
                width=width,equations=equations,cylinders=cylinders,metrics=metrics)


def lift(prepared, point):
    if type(point) is not int or point < 0 or point.bit_length() > prepared['dimension']:
        raise ValueError('invalid active coordinate')
    seed = prepared['seed'].copy()
    for j,mask in enumerate(prepared['coordinates']):
        if not insert(seed,mask,(point >> j) & 1):
            raise ArithmeticError('inconsistent lift')
    word = 0
    for p,(mask,rhs) in sorted(seed.items()):
        word |= (((word & mask).bit_count() & 1) ^ rhs) << p
    if (any((word & mask).bit_count() % 2 != rhs for mask,rhs in prepared['equations'])
            or any(word & mask == target for mask,target in prepared['cylinders'])):
        raise ValueError('point violates original constraints')
    return word


def projected_solve(width,equations,cylinders,*,dimension_cap=None,max_flat_rank=2):
    for bound in (dimension_cap,max_flat_rank):
        if bound is not None and (type(bound) is not int or bound < 0):
            raise ValueError('nonnegative bound required')
    data = prepare(width,equations,cylinders)
    if data['status'] != 'ok':
        return data
    metrics = data['metrics']
    d = data['dimension']
    if max_flat_rank is not None and metrics['residual_rank'] > max_flat_rank:
        return dict(status='unknown',reason='projected rank cap',metrics=metrics)
    if dimension_cap is not None and d > dimension_cap:
        return dict(status='unknown',reason='projected dimension cap',metrics=metrics)
    point = 0
    if data['flats']:
        from affine_cover_solver import solve as cover
        metrics['cover_calls'] += 1
        point = cover(d,data['flats'],kernels=False,separator=False)
        if point is None:
            return dict(status='unsat',metrics=metrics)
    return dict(status='sat',word=lift(data,point),metrics=metrics)


def solve(domains,constraints,output,*,codebooks=None,omission_cap=None,
          dimension_cap=None,max_flat_rank=2):
    data = compile_factors(domains,constraints,output,codebooks=codebooks,omission_cap=omission_cap)
    metrics = data['metrics']
    metrics['queries'] = {}
    witnesses = {}
    def result(status, **fields):
        return dict(status=status,metrics=metrics,witnesses=witnesses,**fields)
    if data['status'] != 'ok':
        return result(data['status'],**({'reason':data['reason']} if 'reason' in data else {}))
    enc,dec,offset,widths = (data[k] for k in ('enc','dec','offset','widths'))
    unknown = None
    for bit in (0,1):
        if bit not in enc[output]:
            continue
        value = enc[output][bit]
        pins = tuple((1 << (offset[output]+j), (value >> j) & 1) for j in range(widths[output]))
        ans = projected_solve(data['width'],data['equations']+pins,data['cylinders'],
                              dimension_cap=dimension_cap,max_flat_rank=max_flat_rank)
        metrics['queries'][bit] = ans['metrics']
        if ans['status'] == 'unknown':
            unknown = ans['reason']
        if ans['status'] == 'sat':
            word = ans['word']
            witness = {v:dec[v][(word >> offset[v]) & ((1 << widths[v])-1)] for v in enc}
            if witness[output] != bit or any((witness[u],witness[v]) not in pairs
                                              for u,v,pairs in data['relations']):
                raise ArithmeticError('original record assignment failed')
            witnesses[bit] = witness
    if unknown is not None:
        return result('unknown',reason=unknown)
    if len(witnesses) == 1:
        return result('constant',value=next(iter(witnesses)))
    return result('pair' if witnesses else 'empty')
