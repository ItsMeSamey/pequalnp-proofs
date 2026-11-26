"""Check Boolean Taylor regrouping on a layout with nontrivial measurements."""
from itertools import product
from math import comb

N = 4
GROUPS = ((0, 1), (2, 3))
POINTS = range(1 << N)


def bit(x, i):
    return (x >> i) & 1


def mul(a, b, q, p):
    c = [0]*(q+1)
    for i, v in enumerate(a):
        for j, w in enumerate(b[:q+1-i]):
            c[i+j] += v*w
    return [x % p if p else x for x in c]


def local(x, u, group, opposite_measurement, q, p):
    # P_i(T)=(1-T)e_i+T e_{first opposite variable}.
    # At t=1 the off-group measurement is the first opposite Boolean coordinate.
    other = GROUPS[1-group]
    local_poly = [1]
    for i in GROUPS[group]:
        slope = bit(u,other[0]) - bit(u,i)
        # Also an identity replacement on i, entering a genuine quadratic
        # product (2+i+x_i) * (1 + theta_i).
        a = 2+i+bit(x,i)
        local_poly = mul(local_poly,[a*(1+opposite_measurement),a*slope],q,p)
    return local_poly


def evaluate(x, u, q, p):
    weights = [bit(x,g[0]) for g in GROUPS]
    return mul(local(x,u,0,weights[1],q,p),local(x,u,1,weights[0],q,p),q,p)


def add(target, term, scale):
    for i, c in enumerate(term):
        target[i] += scale*c


def original(q,p):
    answer = [0]*(q+1)
    for e in POINTS:
        if e.bit_count()>q:
            continue
        for u in POINTS:
            if u & ~e:
                continue
            for x in POINTS:
                if not e & ~x:
                    add(answer,evaluate(x,u,q,p),(-1)**((e^u).bit_count()))
    return answer


def grouped(q,p):
    answer = [0]*(q+1)
    for u in POINTS:
        if u.bit_count()>q:
            continue
        for measurements in product(range(2),repeat=2):
            histogram = {0:[1]}
            for g, variables in enumerate(GROUPS):
                mask = sum(1<<i for i in variables)
                table = {}
                for x in POINTS:
                    if x & ~mask or u & mask & ~x or bit(x,variables[0])!=measurements[g]:
                        continue
                    h = (x & ~u).bit_count()
                    acc = table.setdefault(h,[0]*(q+1))
                    add(acc,local(x,u,g,measurements[1-g],q,p),1)
                combined = {}
                for a, va in histogram.items():
                    for b, vb in table.items():
                        acc = combined.setdefault(a+b,[0]*(q+1))
                        add(acc,mul(va,vb,q,p),1)
                histogram = combined
            for h, poly in histogram.items():
                k = q-u.bit_count()
                b = sum((-1)**j*comb(h,j) for j in range(min(h,k)+1))
                closed = (1 if h==0 else 0) if k>=h else (-1)**k*comb(h-1,k)
                assert b==closed
                add(answer,poly,b)
    return answer


def normalize(a,p):
    return tuple(x%p if p else x for x in a)


if __name__ == '__main__':
    for p in (0,2,3):
        for q in (0,1,2,3,4,5,7):
            direct = [0]*(q+1)
            for x in POINTS:
                add(direct,evaluate(x,x,q,p),1)
            assert normalize(original(q,p),p)==normalize(grouped(q,p),p)==normalize(direct,p)
        print('seven orders verified for modulus',p)
