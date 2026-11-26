"""Exact active coefficient section degrees for two explicit 4-dimensional palettes."""
def bitpar(x):
    return x.bit_count() & 1

def quadratic(x):
    return ((x & 1) & (x >> 1)) ^ ((x >> 2 & 1) & (x >> 3))

def bits(x):
    while x:
        v = x & -x
        yield v.bit_length() - 1
        x ^= v

def encode(values):
    return sum(v << (4 * j) for j,v in enumerate(values))

def elimination(columns):
    pivots = {}
    for j, initial in enumerate(columns):
        v, support = initial, 1 << j
        while v:
            i = v.bit_length()-1
            if i not in pivots:
                pivots[i] = (v, support)
                break
            w, comb = pivots[i]
            v ^= w
            support ^= comb
    def express(v):
        support = 0
        while v:
            i = v.bit_length()-1
            if i not in pivots:
                return None
            w, comb = pivots[i]
            v ^= w
            support ^= comb
        return support
    return express

def analyse(D):
    cols = [(k, (quadratic(k)^1) + 2*s) for k in D for s in (0,1)]
    def tag(g,k):
        return bitpar((g & 15) & k) + 2*bitpar((g >> 4) & k)
    const = elimination([encode(k if tag(g,k)==b else 0 for g in range(256)) for k,b in cols])
    degree2 = [u for u in range(16) if const(encode([u]*256)) is not None]

    # P_k(a) is affine in the first four bits. Its evaluation multiplies the
    # first-lane activation; choose the record agreeing with the second lane.
    terms = [(k,i) for k in D for i in (0,1,2,4,8)]
    def feature(k,i,a):
        return (bitpar(k&a)^quadratic(k)) * int((i&a)==i)
    linear = elimination([encode(k*feature(k,i,a) for a in range(16)) for k,i in terms])
    degree3 = []
    for u in range(16):
        coeff=linear(encode([u]*16))
        if coeff is None:
            continue
        degree3.append(u)
        chosen = [terms[j] for j in bits(coeff)]
        for g in range(256):
            output = 0
            for k,i in chosen:
                if ((g&i)==i) and ((tag(g,k)&1)==(quadratic(k)^1)):
                    assert (k,tag(g,k)) in cols
                    output ^= k
            assert output == u
    return degree2, degree3

if __name__=='__main__':
    D=list(range(1,16))
    whole = analyse(D)
    reduced = analyse([k for k in D if k not in (3,8,11)])
    print('30-record palette, degree 2 and 3:',whole)
    print('24-record palette, degree 2 and 3:',reduced)
    assert whole == (list(range(16)),list(range(16)))
    assert len(reduced[0])==4 and reduced[1]==list(range(16))
