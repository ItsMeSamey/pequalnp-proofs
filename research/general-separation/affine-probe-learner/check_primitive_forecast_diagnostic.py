"""Finite original-assignment checks. No symbolic rewrite or forecast extractor."""
from itertools import product


def dyadic_prefix(end):
    """Maximal aligned blocks in [0,end), generated largest first."""
    start = 0
    result = []
    for k in reversed(range(end.bit_length())):
        if end >> k & 1:
            result.append((start,1 << k))
            start += 1 << k
    return result


def cell(x, start, width, n):
    return all(((x ^ start) >> i) & 1 == 0
               for i in range(width.bit_length()-1,n))


def carries(j,n):
    cells = dyadic_prefix(j) + [(j,1)]
    initial = [any(cell(x,*c,n) for c in cells) for x in range(1 << n)]
    steps = 0
    while len(cells) >= 2:
        (a,s),(b,t) = cells[-2:]
        if s != t or b != a+s or a%(2*s):
            break
        cells[-2:] = [(a,2*s)]
        steps += 1
        for x in range(1 << n):
            assert (cell(x,a,s,n) or cell(x,b,t,n)) == cell(x,a,2*s,n)
    assert cells == dyadic_prefix(j+1)
    assert steps <= n and initial == [x <= j for x in range(1 << n)]


def gray_less(x, params):
    # Fixed template from most significant digit, including padded high bit.
    binary_bit = 0
    equal,less = 1,0
    for i in reversed(range(len(params))):
        binary_bit ^= params[i]
        xbit = (x >> i) & 1
        less |= equal & (1 ^ xbit) & binary_bit
        equal &= 1 ^ xbit ^ binary_bit
    return less


def wires(n,gates,x,mask=None):
    values = [0,1] + [(x >> i) & 1 for i in range(n)]
    if mask is not None:
        values = [mask & bit for bit in values]
    for a,b in gates:
        val = 1 ^ (values[a] & values[b])
        values.append(val if mask is None else mask & val)
    return values


def audit(n,gates,out):
    size = 1 << n
    params = [tuple(((k ^ (k >> 1)) >> i) & 1 for i in range(n+1))
              for k in range(size+1)]
    assert all(sum(a != b for a,b in zip(left,right)) == 1
               for left,right in zip(params,params[1:]))
    for j in range(size):
        carries(j,n)
        target = wires(n,gates,j)
        for x in range(size):
            raw = wires(n,gates,x)
            guard = int(cell(x,j,1,n))
            protected = wires(n,gates,x,guard)
            assert protected == [v & guard for v in raw] == [v & guard for v in target]
            prefix = int(any(cell(x,*c,n) for c in dyadic_prefix(j)))
            nxt = int(any(cell(x,*c,n) for c in dyadic_prefix(j+1)))
            assert (prefix,nxt) == (gray_less(x,params[j]),gray_less(x,params[j+1]))
            assert (raw[out] & nxt) == ((raw[out] & prefix) | protected[out])
            if not target[out]:
                assert (raw[out] & prefix) == (raw[out] & nxt)
            assert gray_less(x,params[0]) == 0 and gray_less(x,params[-1]) == 1


if __name__ == '__main__':
    for n in range(5):
        for out in range(n+2):
            audit(n,[],out)
        for a,b in product(range(n+2),repeat=2):
            audit(n,[(a,b)],n+2)
        first = n+2
        gates = [(n+1,1),(first,first),(first,0),(first+1,first+2)]
        audit(n,gates,first+3)
    print('Dyadic carries, guarded DAG wires and Gray sentinels agree.')
