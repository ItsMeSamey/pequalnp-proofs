"""Exact image search for sparse, possibly high-degree Boolean ANF encoders."""
from collections import deque
from fixed_height import recognize, prior
from hybrid import filtration, minors
from image_solver import normalize
from recognizer import tag_at

def unions(supports,limit):
    queue=deque([(0,0)])
    seen={0}
    while queue:
        current,depth=queue.popleft()
        yield current
        if depth==limit:
            continue
        for extra in supports:
            value=current | extra
            if value not in seen:
                seen.add(value)
                queue.append((value,depth+1))

def solve(columns,d,n,encoder,budgets=()):
    if min(d,n)<0: raise ValueError("negative dimension")
    columns=tuple(columns)
    if any(not (0<=k<1<<d and 0<=b<4 and 0<=h<4) for k,b,h in columns):
        raise ValueError("invalid site coordinates")
    encoder=tuple(normalize(poly,n) for poly in encoder)
    if len(encoder)!=2*d: raise ValueError("expected two encoder coordinates per private key bit")
    supports=sorted({mask for poly in encoder for mask in poly if mask})
    limit=len(supports)
    for s,h in budgets:
        cert=recognize(columns,d,s,h)
        t=d-len(cert.anchors)
        limit=min(limit,min(j+c+2*(t+2) for j,c in filtration(minors(columns,cert),2*d)))
    for assignment in unions(supports,limit):
        chart=sum((sum(m&assignment==m for m in f)%2)<<i for i,f in enumerate(encoder))
        private,lifted,sites={},{},[]
        for idx,(k,b,h) in enumerate(columns):
            if tag_at(chart,k,d)==b:
                prior['add'](private,k)
                if prior['add'](lifted,k<<2|h): sites.append(idx)
        if len(lifted)-len(private)==2: return assignment,sites
    return None
