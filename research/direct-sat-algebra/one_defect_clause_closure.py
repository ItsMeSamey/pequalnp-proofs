"""Sound quadratic-span closure on a 2-CNF relaxation of one marked support."""
from itertools import combinations
from quadratic_target import insert, parity, reduce_vector


def solve_clauses(n,forbidden,pins=()):
    """Implication reachability and greedy consistent assignment; literal 2*i+b means y_i=b."""
    reach=[1<<i for i in range(2*n)]
    for a,b in forbidden:
        reach[a]|=1<<(b^1)
        reach[b]|=1<<(a^1)
    for a in pins:
        reach[a^1]|=1<<a
    for j,r in enumerate(reach):
        for i,v in enumerate(reach):
            if v>>j&1:
                reach[i]|=r
    if any(reach[i]>>(i^1)&reach[i^1]>>i&1 for i in range(0,2*n,2)):
        return None
    chosen=0
    for i in range(n):
        for a in (2*i,2*i+1):
            candidate=chosen|reach[a]
            if not candidate&(candidate>>1)&sum(1<<(2*j) for j in range(n)):
                chosen=candidate
                break
    return sum(((chosen>>(2*i+1))&1)<<i for i in range(n))


def samples(n,H):
    base=solve_clauses(n,H)
    if base is None:
        return []
    flips=[2*i+1-(base>>i&1) for i in range(n)]
    out={base}
    for p in [(a,) for a in flips]+list(combinations(flips,2)):
        if solve_clauses(n,H,p) is None:
            continue
        least=base
        for i,a in enumerate(flips):
            if solve_clauses(n,H,(*p,a^1)) is None:
                least^=1<<i
        out.add(least)
    return sorted(out)


def search(rows,beta,pivot=None):
    n=len(rows)
    if any(v<0 or v>=1<<n for v in (*rows,beta)):
        raise ValueError("invalid matrix or mark")
    if not beta:
        return 'NO',None,0
    if pivot is None:
        pivot=(beta&-beta).bit_length()-1
    if not 0<=pivot<n or not beta>>pivot&1:
        raise ValueError("pivot must be marked")
    def lift(y):
        z=(y&((1<<pivot)-1))|((y>>pivot)<<(pivot+1))
        return z|((1^parity(z&beta))<<pivot)
    # Packed evaluations implement the quotient by all vanishing quadratics.
    N=n-1
    literals=range(2*N)
    candidates={(a,a) for a in literals}|{(a,b) for a,b in combinations(literals,2) if a//2!=b//2}
    H=set()
    rounds=0
    while True:
        rounds+=1
        pts=samples(N,H)
        if not pts:
            return 'NO',None,rounds
        values=[0]*n
        for j,y in enumerate(pts):
            z=lift(y)
            failures=[i for i,r in enumerate(rows) if z>>i&1 and parity(r&z)]
            if not failures:
                return 'YES',z,rounds
            for i in failures:
                values[i]|=1<<j
        space={}
        for v in values:
            insert(v,0,space)
        if not reduce_vector((1<<len(pts))-1,space)[0]:
            return 'NO',None,rounds
        indicators=[sum(1<<j for j,y in enumerate(pts) if y>>(a//2)&1==a%2) for a in literals]
        added={(a,b) for a,b in candidates-H if not reduce_vector(indicators[a]&indicators[b],space)[0]}
        if not added:
            return 'UNKNOWN',None,rounds
        H.update(added)
