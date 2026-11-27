"""Deterministic physical plane search on the image of an explicit Boolean ANF map."""
from itertools import combinations
from fixed_height import recognize, prior
from hybrid import filtration, minors
from recognizer import tag_at

def normalize(poly,n):
    terms=set()
    for mask in poly:
        if not isinstance(mask,int) or not 0<=mask<1<<n:
            raise ValueError("monomial outside assignment domain")
        terms.symmetric_difference_update((mask,))
    return tuple(terms)

def solve(columns,d,n,encoder,budgets):
    if n<0 or d<0: raise ValueError("negative dimension")
    columns=tuple(columns)
    encoder=tuple(normalize(poly,n) for poly in encoder)
    if len(encoder)!=2*d: raise ValueError("expected two chart bits per private dimension")
    degree=max((m.bit_count() for poly in encoder for m in poly),default=0)
    bound=None
    for s,h in budgets:
        cert=recognize(columns,d,s,h)
        t=d-len(cert.anchors)
        for j,c in filtration(minors(columns,cert),2*d):
            candidate=min(n,degree*(j+c+2*(t+2)))
            bound=candidate if bound is None else min(bound,candidate)
    if bound is None: raise ValueError("supply at least one selector budget")
    for size in range(bound+1):
        for active in combinations(range(n),size):
            b=sum(1<<i for i in active)
            chart=sum((sum(mask & b==mask for mask in poly)%2)<<i for i,poly in enumerate(encoder))
            private,physical,sites={},{},[]
            for idx,(k,tag,height) in enumerate(columns):
                if tag_at(chart,k,d)!=tag: continue
                prior['add'](private,k)
                if prior['add'](physical,k<<2|height): sites.append(idx)
            if len(physical)-len(private)==2:
                return bound,(b,sites)
    return bound,None
