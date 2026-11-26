"""Compare incidence-moment attachment against direct weighted CNF enumeration."""
from math import comb
from random import Random

n, ell = 4, 8
mod = 1 << ell
poly = [0]*(2*ell)
for i in range(ell+1):
    for j in range(ell):
        poly[i+j] += (-1)**i*comb(ell,i)*comb(ell+j-1,j)
remainders = []
while poly:
    quot = [0]*max(0,len(poly)-2)
    for i in reversed(range(2,len(poly))):
        quot[i-2] = poly[i]
        poly[i-1] += poly[i]
    remainders.append(poly[:2])
    poly = quot

def coefficient_table(values):
    for i in range(n):
        for s in range(1<<n):
            if s>>i&1:
                values[s] = [(a-b)%mod for a,b in zip(values[s],values[s^(1<<i)])]
    return values

rng = Random(712)
for _ in range(80):
    clauses = [[(rng.randrange(3),rng.randrange(2)) for j in range(3)] for i in range(7)]
    # x3 absent from the CNF, coupled to x0 by a rank-two weight; x2 pinned.
    weights = ((2,-3),(1,4))
    fixed = rng.randrange(2)
    def weight(x):
        return weights[x&1][x>>3&1] * int((x>>2&1)==fixed)
    result = {0:[1]+[0]*(ell-1)}
    direct = 0
    def failed(c,x):
        return int(not any((x>>v&1)==b for v,b in c))
    for x in range(1<<n):
        direct += weight(x)*int(not any(failed(c,x) for c in clauses))
    for i,c in enumerate(clauses):
        values=[]
        for x in range(1<<n):
            y = failed(c,x)+2*(x>>1&1)+2*(i%2)
            values.append([(a+b*y)*pow(y*(y-1),j,mod)%mod for j,(a,b) in enumerate(remainders)])
        coeff=coefficient_table(values)
        nxt={}
        for s,row in result.items():
            for t,f in enumerate(coeff):
                if not any(f):
                    continue
                out=nxt.setdefault(s|t,[0]*ell)
                for j,a in enumerate(row):
                    for k in range(ell-j):
                        out[j+k]=(out[j+k]+a*f[k])%mod
        result=nxt
    total=0
    for s,row in result.items():
        moment=sum(weight(x) for x in range(1<<n) if x&s==s)
        total += sum(row)*moment
    assert (total-direct)%mod==0
    assert (total+mod//2)%mod-mod//2==direct
print('80 weighted dense CNFs, signed decoding, pins and unused coupled bits passed')
