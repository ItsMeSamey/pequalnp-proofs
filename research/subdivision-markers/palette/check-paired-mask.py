from itertools import combinations,product

def span(xs):
    S={0}
    for x in xs:S.update(x^y for y in tuple(S))
    return S
A,B,C,D=16,32,64,128
h1,h2,u,v=1,2,4,8
Fano=span((A,C,D))-{0}
e,f=A^h1^u,B^h2^u
H={0,1,2,3};U=set(range(16))

def tables(E):
    E=list(E)
    k=max(len(span([x>>4 for x in E])).bit_length()-1,0)
    out=set()
    for P in combinations(E,k):
        S=span(P)
        if len({x>>4 for x in S})!=2**k:continue
        out.add(tuple(next(x&15 for x in S if x>>4==q>>4) for q in (A,B)))
    return out
def exact(E):
    E=list(E|{e,f})
    return any(span(P)&U==H for k in range(len(E)+1) for P in combinations(E,k))
def parity(x):return x.bit_count()&1

for attachment in [set(),Fano]:
    E={A,B,A^B^u,B^u,A^v}|attachment
    old=tables(E)
    new=tables(E|{A^u})
    assert new-old=={(u,u)} and not old-new
    assert {(0,0),(u,0),(0,u)}<=old
    assert not exact(E) and exact(E|{A^u})
    assert U<=span(E|{e,f})
    for r,s,K in product(range(16),range(16),range(16)):
        def accepts(t):
            a,b=t
            return ((parity(r&a)^(K&1))*(parity(s&b)^((K>>3)&1)))^((parity(r&b)^((K>>1)&1))*(parity(s&a)^((K>>2)&1)))
        assert any(map(accepts,old))==any(map(accepts,new))
print('two controls, 8192 complete determinant comparisons, exact target verified')
