from itertools import combinations

def span(xs):
    s={0}
    for x in xs:
        s.update(x^y for y in tuple(s))
    return frozenset(s)

def witnesses(E):
    return [span(F) for n in range(len(E)+1) for F in combinations(E,n)]

U=span([1,2,4,8])
E=[16,17,20,21,24,26,28,31]
cached=[]
for cols in [E,E+[18],[16+x for x in (0,1,2,4,8,15)]]:
    W=set(witnesses(cols))
    K={S&U for S in W}
    assert len([s for s in K if len(s)==2])==15
    lines=[S for S in W if len(S&U)==2]
    for A,B in combinations(lines,2):
        if A&U==B&U:
            continue
        image=lambda S:{x>>4 for x in S}
        lhs=len(image(A)&image(B))
        rhs=len(A&B)
        assert len(span(A|B)&U)*rhs==4*lhs
    cached.append(K)
assert len(cached[0])==65 and len(cached[1])==67
for h in U-{0}:
    quotient=lambda K:{frozenset(min(x,x^h) for x in s) for s in K}
    assert len(quotient(cached[0]))==len(quotient(cached[1]))==16
assert span([1,2]) not in cached[0] and span([1,6]) not in cached[2]
print('three full-line controls and all 15 quotient spectra verified')
