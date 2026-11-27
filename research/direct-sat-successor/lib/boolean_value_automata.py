"""Capped synchronous GF(2) wire compiler. Affine mask convention as backward_bank.py."""


class BudgetExceeded(Exception):
    pass


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def dot(a, b):
    return (a & b).bit_count() & 1


def apply(row, matrix):
    out = 0
    for j in indices(row):
        out ^= matrix[j]
    return out


def pair(a, b, width):
    out = 0
    for i in indices(a):
        out |= b << (i * width)
    return out


def insert(table, value, coordinate):
    for j in sorted(table, reverse=True):
        if value >> j & 1:
            p, c = table[j]
            value ^= p
            coordinate ^= c
    if not value:
        return False
    table[value.bit_length() - 1] = value, coordinate
    return True


def coordinates(table, val):
    result = 0
    for j in sorted(table, reverse=True):
        if val >> j & 1:
            p, c = table[j]
            val ^= p
            result ^= c
    if val:
        raise AssertionError('signature outside basis span')
    return result


def profile(row, columns):
    return sum(dot(row, c) << j for j, c in enumerate(columns))


def minimize(program):
    dims, initial, transitions, final = program
    n = len(transitions)
    suffix = [None] * (n + 1)
    suffix[n] = [final] if final else []
    for i in reversed(range(n)):
        vectors = []
        basis = {}
        for matrix in transitions[i]:
            for c in suffix[i+1]:
                s = sum(dot(r,c) << j for j,r in enumerate(matrix))
                if insert(basis,s,0):
                    vectors.append(s)
        suffix[i] = vectors
    # At each cut retain ACTUAL reached rows, independent after suffix evaluation.
    current = [(initial,0)] if profile(initial,suffix[0]) else []
    widths = [len(current)]
    packed = []
    for i in range(n):
        basis = {}
        following = []
        new_matrices = []
        for bit, matrix in enumerate(transitions[i]):
            entries = []
            for row, word in current:
                reached = apply(row,matrix)
                sig = profile(reached,suffix[i+1])
                if insert(basis,sig,1 << len(following)):
                    entries.append(1 << len(following))
                    following.append((reached,word | bit << i))
                else:
                    entries.append(coordinates(basis,sig))
            new_matrices.append(tuple(entries))
        packed.append(tuple(new_matrices))
        current = following
        widths.append(len(current))
    end = sum(dot(row,final)<<j for j,(row,_) in enumerate(current))
    witness = next((word for row,word in current if dot(row,final)), None)
    return (widths,int(bool(widths[0])),packed,end), witness


def solve(n, gates, output, *, order=None, budget=1000000):
    order = tuple(range(n)) if order is None else tuple(order)
    if sorted(order) != list(range(n)) or budget < 0:
        raise ValueError('invalid raw order or budget')
    if output < 0 or output.bit_length() > n+len(gates)+1:
        raise ValueError('invalid output mask')
    for j,(a,b) in enumerate(gates):
        if min(a,b)<0 or max(a,b).bit_length()>n+j+1:
            raise ValueError('invalid operand mask')
    cost = {'budget':budget,'charged_cells':0,'operations':0,'max_pre_width':0,'max_min_width':0}

    def reserve(d):
        # Dense scalar slots for both matrices per layer plus cut vectors;
        # polynomial elimination/bit-arithmetic overhead is outside this metric.
        cells = 1+sum(d)+2*sum(a*b for a,b in zip(d,d[1:]))
        if cost['charged_cells']+cells>budget:
            cost['declined_cells']=cells
            raise BudgetExceeded
        cost['charged_cells']+=cells
        cost['operations']+=1
        cost['max_pre_width']=max(cost['max_pre_width'],max(d))

    def compact(p):
        result, w = minimize(p)
        cost['max_min_width']=max(cost['max_min_width'],max(result[0]))
        return result,w

    def atom(index):
        d = [1]*(n+1)
        reserve(d)
        matrix=[((1,),(1,)) for _ in range(n)]
        if index is not None:
            matrix[index]=((0,),(1,))
        return d,1,matrix,1

    def combine(p,q,product):
        a,s,psteps,t=p
        b,u,qsteps,v=q
        d=[x*y if product else x+y for x,y in zip(a,b)]
        reserve(d)
        steps=[]
        for i,(pm,qm) in enumerate(zip(psteps,qsteps)):
            layer=[]
            for m1,m2 in zip(pm,qm):
                if product:
                    rows=tuple(pair(x,y,b[i+1]) for x in m1 for y in m2)
                else:
                    rows=tuple(m1)+tuple(y<<a[i+1] for y in m2)
                layer.append(rows)
            steps.append(tuple(layer))
        if product:
            return compact((d,pair(s,u,b[0]),steps,pair(t,v,b[-1])))[0]
        return compact((d,s | u<<a[0],steps,t | v<<a[-1]))[0]

    try:
        constant=atom(None)
        zero=([0]*(n+1),0,[((),())]*n,0)
        wires=[constant]+[None]*n
        for pos,raw in enumerate(order):
            wires[raw+1]=atom(pos)
        def affine(mask):
            selected=[wires[i] for i in indices(mask)]
            if not selected:
                return zero
            acc=selected[0]
            for item in selected[1:]:
                acc=combine(acc,item,False)
            return acc
        for a,b in gates:
            wires.append(combine(affine(a),affine(b),True))
        out=affine(output)
        reserve(out[0])
        _,word=compact(out)
        if word is None:
            return {'status':'unsat','cost':cost}
        witness=sum(((word>>i)&1)<<v for i,v in enumerate(order))
        actual=1|(witness<<1)
        for j,(a,b) in enumerate(gates):
            actual |= (dot(actual,a)&dot(actual,b))<<(n+j+1)
        if not dot(actual,output):
            raise AssertionError('original witness failed replay')
        return {'status':'sat','witness':witness,'cost':cost}
    except BudgetExceeded:
        return {'status':'skip','cost':cost}
