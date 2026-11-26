"""Compare exact local flux-table convolution against original raw witnesses."""
import random
rng = random.Random(63712)
def total(bits, labels):
    value = 0
    for i, label in enumerate(labels):
        if bits >> i & 1:
            value ^= label
    return value
def cut(phi, columns):
    return sum(((phi & v).bit_count() % 2) << i for i, v in enumerate(columns))
def models(cols, left, right, rank):
    scores = {}
    for phi in range(1 << rank):
        d = cut(phi, cols)
        for c in range(1 << len(cols)):
            if c & d == 0 and total(c, cols) == 0:
                scores[total(c, left) ^ total(d, right)] = (c,d)
    return scores
checked = 0
for trial in range(80):
    b = rng.randrange(3)
    rank = b + 3
    parts = []
    for i in range(3):
        cols = [(1 << (b + i)) ^ rng.randrange(1 << b) for _ in range(rng.randrange(1,4))]
        parts.append(cols)
    if b:
        parts.append([1])
    cols = sum(parts, [])
    left = [rng.randrange(16) for _ in cols]
    right = [rng.randrange(16) for _ in cols]
    exact = models(cols, left, right, rank)
    output = {}
    for delta in range(1 << b):
        dp = {(0,0):(0,0)}
        offset = 0
        for part in parts:
            local = {}
            for a in range(1 << rank):
                if a % (1 << b) != delta:
                    continue
                d = cut(a, part)
                for c in range(1 << len(part)):
                    w = total(c, part)
                    if c & d or w >= 1 << b:
                        continue
                    gain = total(c, left[offset:]) ^ total(d, right[offset:])
                    local[w,gain] = c,d
            dp = {(x^u,y^v):(c|(e<<offset),d|(f<<offset))
                  for (x,y),(c,d) in dp.items() for (u,v),(e,f) in local.items()}
            offset += len(part)
        output.update({s:pair for (w,s),pair in dp.items() if w==0})
    assert set(output)==set(exact)
    dual = {cut(phi,cols) for phi in range(1<<rank)}
    for s,(c,d) in output.items():
        assert d in dual and not c&d and not total(c,cols)
        assert total(c,left)^total(d,right)==s
        checked+=1
print(80, 'instances,',checked,'physical witnesses verified')
