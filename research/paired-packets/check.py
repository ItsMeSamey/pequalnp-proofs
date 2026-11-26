"""Contract source Cauchy packets on affine flows with local quadratic syndromes."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import prod


def toggle(polynomial, monomial):
    if monomial in polynomial:
        polynomial.remove(monomial)
    else:
        polynomial.add(monomial)


def gauss(d, polynomial):
    polynomial=set(polynomial)
    pairs=0
    while True:
        edge=next((m for m in polynomial if m.bit_count()==2),None)
        if edge is None:
            if any(m for m in polynomial):
                return 0
            return (-1 if 0 in polynomial else 1)*2**(d-pairs)
        i=edge&-edge
        j=edge^i
        left={m^i for m in polynomial if m&i and m!=edge}
        right={m^j for m in polynomial if m&j and m!=edge}
        polynomial={m for m in polynomial if not m&edge}
        for a,b in product(left,right):
            toggle(polynomial,a|b)
        pairs+=1


def qvalue(q,x):
    return sum(m&x==m for m in q)%2


def incidence(edges):
    return {v:[i for i,(a,b) in enumerate(edges) if v in (a,b)] for v in sorted({v for e in edges for v in e})}


def local_quadratics(incident):
    return {v:{(1<<i)|(1<<j) for i,j in combinations(es,2)} for v,es in incident.items()}


def global_quadratic(local):
    q=set()
    for terms in local.values():
        q.symmetric_difference_update(terms)
    return q


def local_valid(side,x,h,inc,local):
    return all(sum((h>>e)&1 for e in inc[v])%2==qvalue(local[v],x) for v in side)


@lru_cache(None)
def W(L,T,x,y):
    skip=y-x
    nodes=range(-L,L)
    return Fraction(prod(T-q for q in nodes if q!=skip),prod(-q for q in nodes if q!=0))


def packets(m,T):
    L=8
    ans=[]
    for e in range(m):
        for layer in range(2):
            y=2
            # Pinned rows are distinct from the distinguished slot. Their number
            # and positions vary, but the two copies in a complementary pair match.
            pinned=((0,4),(4,6),(0,6))[(e+layer)%3]
            w=W(L,T,y,y)
            P=prod(1-W(L,T,x,y) for x in pinned)
            ans.append(((1,P*(1-w)),(0,P*w)))
    return ans


def check_full(edges,T):
    inc=incidence(edges); loc=local_quadratics(inc); m=len(edges)
    left={a for a,b in edges}; right={b for a,b in edges}
    mats=packets(m,T)
    # Independent endpoint tensor contractions before imposing K support.
    ys=[(x,h) for x,h in product(range(1<<m),repeat=2) if local_valid(left,x,h,inc,loc)]
    xs=[(x,h) for x,h in product(range(1<<m),repeat=2) if local_valid(right,x,h,inc,loc)]
    direct=0
    for yu,xu in product(ys,xs):
        val=1
        for e in range(m):
            for layer in range(2):
                y=(yu[layer]>>e)&1
                x=(xu[layer]>>e)&1
                K=mats[2*e+layer]
                val*=K[y][x]*K[1-y][1-x]
            if not val: break
        direct+=val
    q=global_quadratic(loc)
    count=(2**m+gauss(m,q))//2*2**(m-len(inc)+1)
    assert direct==count*prod(K[1][1] for K in mats)
    return count


def check_merged(edges):
    inc=incidence(edges); loc=local_quadratics(inc)
    m=len(edges); q=global_quadratic(loc)
    brute=sum(local_valid(inc,x,h,inc,loc) for x,h in product(range(1<<m),repeat=2))
    predicted=(2**m+gauss(m,q))//2*2**(m-len(inc)+1)
    assert brute==predicted
    return predicted


square=[(i,j) for i in range(2) for j in (2,3)]
for T in (0,1,17,33,-15):
    print("full Cauchy evaluation",T,"underlying count",check_full(square,T))
print("K3,3 merged comparison",check_merged([(i,j) for i in range(3) for j in (3,4,5)]))

from itertools import permutations


def valuation(frac):
    def integer(v):
        return (abs(v)&-abs(v)).bit_length()-1
    return integer(frac.numerator)-integer(frac.denominator)


def mode_fixture():
    L,T,y=8,17,2
    # N=C(T)/C'(0); here v_2(N)=4 since log_2(L)=3.
    N=W(L,T,y,y)*T
    assert valuation(N)==L.bit_length()
    local=[]
    for slot in range(8):
        frozen=((0,4),(4,6),(0,6))[slot%3]
        rs=(y,)+frozen
        vals=[]
        for B in ((0,),(1,),(0,1)):
            # Live Y=1 requires one mode; inject all others into Y=0 rows.
            val=0
            for rows in permutations(rs,len(B)):
                if y not in rows:
                    continue
                val+=(-1)**(len(B)-1)*prod(N*2**b/(T+x)**(b+1) for x,b in zip(rows,B))
            vals.append(val)
        assert all(vals)
        local.append(vals)
    assert all(sum(valuation(v) for v in vs)<256 for vs in product(*local))
    print("6561 distinct supported mode configurations survive modulo 2^256")


mode_fixture()

# Full all-neighbor phase admits an independent closed form on balanced bipartite graphs.
for n,m,actual in [(4,4,24),(6,9,5120)]:
    assert actual==2**(m-n+1)*(2**m+2**(m-n//2+1))//2

# Perturb local predicates on the same K3,3 topology without changing any packet transfer.
edges=[(i,j) for i in range(3) for j in (3,4,5)]
inc=incidence(edges)
loc=local_quadratics(inc)
expected=[]
for v,term in ((None,None),(0,1<<0),(1,(1<<3)|(1<<4)),(3,0)):
    if v is not None: toggle(loc[v],term)
    q=global_quadratic(loc)
    primary=sum(qvalue(q,z)==0 for z in range(1<<9))
    assert primary==(2**9+gauss(9,q))//2
    expected.append(primary*2**4)
print("same-graph heterogeneous predicates",expected)
