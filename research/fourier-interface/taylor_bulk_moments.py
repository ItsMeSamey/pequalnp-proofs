"""Exact bulk diagonal evaluation by baseline subset sums and directional moments."""
from itertools import product
from math import comb, prod
from collections import defaultdict


def indices(weights,q):
    return [a for a in product(*(range(q//w+1) for w in weights))
            if sum(i*w for i,w in zip(a,weights))<=q]


def directional_moments(columns,weights,q,mod):
    alphas = indices(weights,q)
    zero = (0,)*len(weights)
    empty = (0,)*len(columns[0][0])
    current = {empty:{a:int(a==zero) for a in alphas}}
    reduce = (lambda v:v%mod) if mod else (lambda v:v)
    for base,shift in columns:
        after = {s:dict(m) for s,m in current.items()}
        for s,m in current.items():
            t = tuple(reduce(v+b) for v,b in zip(s,base))
            target = after.setdefault(t,dict.fromkeys(alphas,0))
            for a in alphas:
                value = sum(m[b]*prod(comb(j,i)*v**(j-i)
                                      for i,j,v in zip(b,a,shift))
                            for b in product(*(range(j+1) for j in a)))
                target[a] = reduce(target[a]+value)
        current = after
    return current


def times(left,right,q):
    result = defaultdict(int)
    for (j,a),v in left.items():
        for (k,b),w in right.items():
            if j+k<=q:
                result[j+k,tuple(i+l for i,l in zip(a,b))] += v*w
    return result


def evaluate(columns,weights,rows,q,mod):
    # Product of factors (1+theta), with each row carrying base coefficients
    # and a list of (positive z order, direction index, scalar coefficient).
    moments = directional_moments(columns,weights,q,mod)
    zero = (0,)*len(weights)
    answer = [0]*(q+1)
    for s,m in moments.items():
        value = {(0,zero):1}
        for base,terms in rows:
            factor = defaultdict(int,{(0,zero):1+sum(i*j for i,j in zip(s,base))})
            for j,d,c in terms:
                assert j>=weights[d]
                if j<=q:
                    unit = tuple(int(i==d) for i in range(len(weights)))
                    factor[j,unit] += c
            value = times(value,factor,q)
        for (j,a),v in value.items():
            answer[j] += v*m[a]
    return [v%mod if mod else v for v in answer]


def direct(columns,rows,q,mod):
    result = [0]*(q+1)
    for bits in product((0,1),repeat=len(columns)):
        value = [1]+[0]*q
        for baseline,terms in rows:
            factor = [1]+[0]*q
            for active,(base,directions) in zip(bits,columns):
                if active:
                    factor[0] += sum(i*j for i,j in zip(base,baseline))
                    for j,d,c in terms:
                        if j<=q:
                            factor[j] += c*directions[d]
            value = [sum(value[i]*factor[j-i] for i in range(j+1)) for j in range(q+1)]
        result = [a+b for a,b in zip(result,value)]
    return [v%mod if mod else v for v in result]


if __name__=='__main__':
    columns = [((i%2,int(i%3==0)),(2**i,(-3)**i,5*i-7)) for i in range(8)]
    weights = (1,2,3)
    rows = [((j%3,2-j),[(1,0,j-2),(2,1,1),(3,0,-j),(3,2,2)])
            for j in range(6)]
    for mod in (0,2,3,8):
        for q in (0,1,2,3,4,6,9):
            assert evaluate(columns,weights,rows,q,mod)==direct(columns,rows,q,mod)
    print('28 full diagonal comparisons passed; no two full input columns identical')
