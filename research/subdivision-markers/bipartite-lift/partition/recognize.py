"""Recognize binary alternating matrices with sum of two same-shore ranks ≤k."""
from itertools import combinations


def inverse(rows):
    n = len(rows)
    aug = [row | (1 << (n+i)) for i,row in enumerate(rows)]
    for j in range(n):
        pivot = next((i for i in range(j,n) if (aug[i] >> j) & 1), None)
        if pivot is None:
            return None
        aug[j], aug[pivot] = aug[pivot], aug[j]
        for i in range(n):
            if i != j and (aug[i] >> j) & 1:
                aug[i] ^= aug[j]
    return [row >> n for row in aug]


def profile(rows, base):
    """Return C G^-1 and columns C indexed by vertex, or None for singular G."""
    columns = [sum(((row >> b) & 1) << j for j,b in enumerate(base)) for row in rows]
    inv = inverse([columns[b] for b in base])
    if inv is None:
        return None
    dual = []
    for x in columns:
        y = 0
        while x:
            bit = x & -x
            y ^= inv[bit.bit_length()-1]
            x ^= bit
        dual.append(y)
    return dual,columns


def twosat(n, forbidden, bases):
    # Literal 2*v+s means vertex v has shore s. A forbidden monochromatic
    # pair gives two implications. A forced base vertex gives a unit clause.
    out = [[] for _ in range(2*n)]
    rev = [[] for _ in range(2*n)]
    def imply(x,y):
        out[x].append(y)
        rev[y].append(x)
    for u,v,s in forbidden:
        x,y = 2*u+s,2*v+s
        imply(x,y^1)
        imply(y,x^1)
    for s,base in enumerate(bases):
        for v in base:
            imply((2*v+s)^1,2*v+s)
    seen = set()
    order = []
    for start in range(2*n):
        if start in seen:
            continue
        stack = [(start,0)]
        seen.add(start)
        while stack:
            x,j = stack[-1]
            if j == len(out[x]):
                order.append(x)
                stack.pop()
            else:
                y = out[x][j]
                stack[-1] = (x,j+1)
                if y not in seen:
                    seen.add(y)
                    stack.append((y,0))
    component = [-1]*(2*n)
    for c,x in enumerate(reversed(order)):
        if component[x] >= 0:
            continue
        component[x] = c
        stack = [x]
        while stack:
            for y in rev[stack.pop()]:
                if component[y] < 0:
                    component[y] = c
                    stack.append(y)
    if any(component[2*v] == component[2*v+1] for v in range(n)):
        return None
    return tuple(int(component[2*v+1] > component[2*v]) for v in range(n))


def recognize(rows,k):
    """Return (colors, left_basis, right_basis), or None if no partition fits."""
    n = len(rows)
    if any(row < 0 or row >> n or (row >> i) & 1 for i,row in enumerate(rows)):
        raise ValueError('matrix must be binary alternating with the supplied order')
    if any(((rows[u] >> v) ^ (rows[v] >> u)) & 1 for u,v in combinations(range(n),2)):
        raise ValueError('matrix must be symmetric')
    for total in range(0,min(n,k)+1,2):
        for p in range(0,total//2+1,2):  # swap colors so the left rank is smaller
            for left in combinations(range(n),p):
                lp = profile(rows,left)
                if lp is None:
                    continue
                rest = sorted(set(range(n)) - set(left))
                for right in combinations(rest,total-p):
                    rp = profile(rows,right)
                    if rp is None:
                        continue
                    forbidden = ((u,v,s) for s,(dual,cols) in enumerate((lp,rp))
                                 for u,v in combinations(range(n),2)
                                 if (((rows[u] >> v) & 1) !=
                                     ((dual[u] & cols[v]).bit_count() & 1)))
                    colors = twosat(n,forbidden,(left,right))
                    if colors is not None:
                        return colors,left,right
    return None
