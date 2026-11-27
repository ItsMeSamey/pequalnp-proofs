"""Single-mark support via actual feasible generators on an SCC prefix."""
from collections import deque
from quadratic_target import insert, parity


def blocks(rows):
    """Topological SCC order for arcs j -> i whenever row i reads j."""
    n=len(rows)
    reach=[sum(1<<i for i,r in enumerate(rows) if r>>j&1)|(1<<j) for j in range(n)]
    for j in range(n):
        for i in range(n):
            if reach[i]>>j&1:
                reach[i]|=reach[j]
    left=set(range(n))
    while left:
        j=max(left,key=lambda i:((reach[i]&sum(1<<v for v in left)).bit_count(),-i))
        component=sorted(i for i in left if reach[i]>>j&1 and reach[j]>>i&1)
        left.difference_update(component)
        yield component


def symmetric_generators(rows):
    """Zero-diagonal singleton supports and induced paths with marked endpoints."""
    n=len(rows)
    marked={i for i in range(n) if rows[i]>>i&1}
    for i in range(n):
        if i not in marked:
            yield 1<<i
    for i in sorted(marked):
        queue=deque([(i,1<<i)])
        seen={i}
        while queue:
            j,path=queue.popleft()
            for k in range(n):
                if k in seen or not rows[j]>>k&1:
                    continue
                seen.add(k)
                extended=path|(1<<k)
                if k not in marked:
                    queue.append((k,extended))
                elif k>i:
                    yield extended


def search(rows,beta,*,local_cap=10):
    """Return YES/NO/UNKNOWN, an actual witness if YES, and diagnostic ranks."""
    n=len(rows)
    if local_cap<0 or any(not 0<=v<1<<n for v in (*rows,beta)):
        raise ValueError("invalid matrix, mark, or local cap")
    reps=[]
    pivots={}
    trace=[]
    for C in blocks(rows):
        def incoming(x):
            return sum(parity(rows[i]&x)<<j for j,i in enumerate(C))
        shifted={0:0}
        image={}
        for x in reps:
            h=incoming(x)
            insert(h,0,image)
            shifted.setdefault(h,x)
        local=[sum(((rows[i]>>j)&1)<<k for k,j in enumerate(C)) for i in C]
        symmetric=all((r>>j^local[j]>>i)&1==0 for i,r in enumerate(local) for j in range(i))
        trace.append((tuple(C),len(image),symmetric))
        if len(image)>1 or (not symmetric and len(C)>local_cap):
            return 'UNKNOWN',None,trace
        for h,prefix in shifted.items():
            moved=[r^(((h>>i)&1)<<i) for i,r in enumerate(local)]
            if symmetric:
                generators=symmetric_generators(moved)
            else:
                generators=(z for z in range(1<<len(C))
                            if all(not(z>>i&1 and parity(r&z)) for i,r in enumerate(moved)))
            for z in generators:
                x=prefix|sum(((z>>j)&1)<<i for j,i in enumerate(C))
                if parity(x&beta):
                    return 'YES',x,trace
                if insert(x,0,pivots):
                    reps.append(x)
    return 'NO',None,trace
