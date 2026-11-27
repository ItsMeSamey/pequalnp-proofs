"""Probe a monotone DAG on affine forms of freely writable physical bits.

Nodes in topological order are ('leaf', mask, offset), ('and', *child_ids),
or ('or', *child_ids). The last node is the root. Empty AND/OR are constants.
The conditional constant verdict assumes predict(construct(key)) equals the
given representation for every key. Endpoint agreement cannot prove fidelity.
"""


def _endpoint(leaves, target):
    pivots = {}
    for mask, offset in leaves:
        rhs = offset ^ target
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = mask, rhs
                break
            row, value = pivots[pivot]
            mask ^= row
            rhs ^= value
        else:
            if rhs:
                return None
    key = 0
    for pivot in sorted(pivots):
        row, rhs = pivots[pivot]
        if (row & key).bit_count() % 2 != rhs:
            key |= 1 << pivot
    return key


def probe(width, nodes, construct, predict, *, promised=False):
    """Return physically checked samples and a pair, conditional constant, or unknown."""
    if type(width) is not int or width < 0:
        raise ValueError('expected nonnegative physical width')
    nodes = tuple(tuple(node) for node in nodes)
    if not nodes:
        raise ValueError('missing root')
    # Dead leaves must not constrain endpoint feasibility.
    live = {len(nodes) - 1}
    leaves = []
    bounds = {}
    for i in range(len(nodes) - 1, -1, -1):
        if i not in live:
            continue
        op, *args = nodes[i]
        if op == 'leaf':
            mask, offset = args
            if type(mask) is not int or mask < 0 or mask.bit_length() > width:
                raise ValueError('invalid affine mask')
            if type(offset) is not int or offset not in (0, 1):
                raise ValueError('invalid affine offset')
            # A zero mask is a fixed literal, even at formal endpoints.
            if mask:
                leaves.append((mask, offset))
            bounds[i] = (0, 1) if mask else (offset, offset)
        elif op in ('and', 'or'):
            if any(type(j) is not int or not 0 <= j < i for j in args):
                raise ValueError('expected a topologically earlier child')
            live.update(args)
        else:
            raise ValueError('unrecognized operation')
    for i in sorted(live):
        op, *args = nodes[i]
        if op != 'leaf':
            gate = all if op == 'and' else any
            bounds[i] = tuple(int(gate(bounds[j][t] for j in args)) for t in (0, 1))
    lower, upper = bounds[len(nodes) - 1]
    samples = []
    mismatch = False
    for target, expected in enumerate((lower, upper)):
        key = _endpoint(leaves, target)
        if key is None:
            continue
        raw = construct(key)
        bit = predict(raw)
        if type(bit) not in (int, bool) or bit not in (0, 1):
            raise ValueError('predict must return a bit')
        mismatch |= bit != expected
        samples.append(dict(target=target, key=key, physical=raw, prediction=int(bit)))
    result = dict(samples=samples)
    if mismatch:
        return dict(result, status='unknown', reason='endpoint mismatch')
    if len(samples) == 2 and samples[0]['prediction'] != samples[1]['prediction']:
        return dict(result, status='pair')
    if samples and lower == upper:
        if not promised:
            return dict(result, status='unknown', reason='representation unpromised')
        return dict(result, status='constant', value=lower, conditional_on_representation=True)
    return dict(result, status='unknown', reason='infeasible endpoint')
