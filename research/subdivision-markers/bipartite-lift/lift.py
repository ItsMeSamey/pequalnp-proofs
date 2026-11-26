"""Binary row masks and vertex masks, with vertices in L before vertices in R."""


def dot(a,b):
    return (a & b).bit_count() % 2


def transpose(rows, width):
    return [sum(((row >> j) & 1) << i for i,row in enumerate(rows)) for j in range(width)]


def apply(rows,x):
    return sum(dot(row,x) << i for i,row in enumerate(rows))


def reduce_vector(x,pivots):
    for j in sorted(pivots,reverse=True):
        if x >> j & 1:
            x ^= pivots[j]
    return x


def basis(vectors):
    pivots = {}
    for x in vectors:
        x = reduce_vector(x,pivots)
        if x:
            pivots[x.bit_length()-1] = x
    return pivots


def kernel(rows,n):
    pivots = basis(rows)
    result = []
    for i in range(n):
        if i in pivots:
            continue
        x = 1 << i
        for j in sorted(pivots):
            x |= dot(x,pivots[j]) << j
        result.append(x)
    return result


def optimum(rows,l):
    n = len(rows)
    if not 0 <= l <= n or any(row < 0 or row.bit_length()>n for row in rows):
        raise ValueError("invalid square matrix or partition")
    r = n-l
    low = (1 << l)-1
    a = [x & low for x in rows[:l]]
    b = [x >> l for x in rows[:l]]
    c = [x & low for x in rows[l:]]
    d = [x >> l for x in rows[l:]]
    im_a = basis(transpose(a,l))
    im_d = basis(transpose(d,r))
    f = [x^y for x,y in zip(b,transpose(c,l))]
    columns = transpose(f,r)
    # E=P F, where P projects onto im A. Elimination is linear.
    e = transpose([v ^ reduce_vector(v,im_a) for v in columns],l)
    cross = [u^v for u,v in zip(b,e)]
    left = [a[i] | (e[i]<<l) for i in range(l)]
    right = [(u^v) | (w<<l) for u,v,w in zip(c,transpose(cross,r),d)]
    k = kernel(transpose(d,r),r)
    defect = len(basis(reduce_vector(apply(f,x),im_a) for x in k))
    return cross,left,right,len(im_a)+len(im_d)+defect


def factors(rows):
    # Row basis as the list of auxiliary value masks; expand each row in it.
    pivots = basis(rows)
    js = sorted(pivots,reverse=True)
    v = [pivots[j] for j in js]
    u = []
    for x in rows:
        mask = 0
        for k,j in enumerate(js):
            if x >> j & 1:
                mask |= 1 << k
                x ^= pivots[j]
        assert not x
        u.append(mask)
    return u,v


def build(rows,l):
    n = len(rows)
    cross,left,right,overhead = optimum(rows,l)
    shore = [0]*l + [1]*(n-l)
    edges = []
    def vertex(side):
        shore.append(side)
        return len(shore)-1
    for i,row in enumerate(cross):
        edges.extend((i,l+j) for j in range(n-l) if row >> j & 1)
    markers = []
    for side,start,matrix in [(0,0,left),(1,l,right)]:
        u,v = factors(matrix)
        for j,mask in enumerate(v):
            aux = vertex(1-side)
            markers.append((aux,mask))
            edges.extend((start+i,aux) for i,x in enumerate(u) if x >> j & 1)
    hub = vertex(0)
    spokes = []
    for aux,_ in markers:
        path = [aux,vertex(1-shore[aux])]
        if shore[aux] != shore[hub]:
            path.append(vertex(1-shore[path[-1]]))
        path.append(hub)
        edges.extend(zip(path,path[1:]))
        spokes.append(path[1:-1])
    assert overhead == len(markers)
    return shore,edges,markers,hub,spokes


def extend(x,graph):
    shore,edges,markers,hub,spokes = graph
    s = x | (1 << hub)
    for aux,mask in markers:
        s |= dot(x,mask) << aux
    preliminary = s
    for (aux,_),interior in zip(markers,spokes):
        if not (s >> aux & 1):
            continue
        deg = sum((preliminary >> (b if a == aux else a)) & 1
                  for a,b in edges if aux in (a,b))
        if deg % 2:
            for j in interior:
                s |= 1 << j
    return s
