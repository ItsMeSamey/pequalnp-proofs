"""Enumerate matrix-index walks and signed monomial choices before degree lookup."""
from itertools import product
from collections import Counter

# Entry is (row, column, sign, u-degree, v-degree); omit zeros.
A=[(0,2,1,0,0),(1,0,1,0,0),(1,2,-1,0,1),(2,1,1,0,0),(2,2,1,1,0)]
B=[(0,0,1,0,1),(0,1,1,0,0),(1,0,-1,1,0),(1,2,1,0,0),(2,0,1,0,0)]
def terms(turns):
    for entries in product(*(A if t==1 else B for t in turns)):
        if all(e[1]==entries[(i+1)%len(entries)][0] for i,e in enumerate(entries)):
            sign=(-1)**sum(e[2]<0 for e in entries)
            yield sign,sum(e[3] for e in entries),sum(e[4] for e in entries)

def check(loops):
    pos=sum(sum(loop)==1 for loop in loops)
    neg=len(loops)-pos
    hist=Counter()
    raw=[]
    for choice in product(*(terms(loop) for loop in loops)):
        a=sum(e[1] for e in choice)
        b=sum(e[2] for e in choice)
        sign=(-1)**sum(e[0]<0 for e in choice)
        hist[a,b]+=sign
        raw.append((a,b,sign))
    assert {p:c for p,c in hist.items() if c}=={(pos,neg):1}
    # Delta functions span *every* lookup. Also run concrete non-linear lookups
    # with arbitrary values on keys outside the surviving range.
    for f in [lambda a,b: (a+2*b)%3==2, lambda a,b: a==0,
              lambda a,b: a*b%2==1 or a>pos, lambda a,b: a+b==0]:
        assert sum(s*f(a,b) for a,b,s in raw)==f(pos,neg)
        assert sum(s*f(a,0) for a,b,s in raw)==f(pos,0)
    return len(raw)

mixed=[(1,-1,1),(-1,1,-1),(1,1,-1,1,-1),(-1,-1,1,-1,1)]
cases=[()]+[(u,) for u in mixed]+list(product(mixed,repeat=2))
print(len(cases),'loop systems;',sum(check(c) for c in cases),'signed degree records checked')
