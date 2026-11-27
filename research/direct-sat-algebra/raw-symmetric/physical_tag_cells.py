"""Output-polynomial deterministic tag-cell enumeration on original column indices."""
from itertools import combinations
from physical_omega_gim import anchored, indices
from quadratic_centroid import independent


def fundamental(cols,mask):
    """Fundamental circuits of one greedy basis, as original-index masks."""
    pivots={}
    relations=[]
    for j in indices(mask):
        v,word=cols[j],1<<j
        while v:
            k=v.bit_length()-1
            if k not in pivots:
                pivots[k]=v,word
                break
            x,z=pivots[k]
            v,word=v^x,word^z
        else:
            relations.append(word)
    return relations


def through(cols,a):
    """Dual not implicit here: cols represents the actual circuit matroid."""
    full=(1<<len(cols))-1
    roots=fundamental(cols,full)
    component=1<<a
    while True:
        previous=component
        for c in roots:
            if c&component:
                component|=c
        if previous==component:
            break
    circuits=[c for c in roots if c&component]
    k=0
    while k<len(circuits):
        c=circuits[k]
        if c>>a&1:
            yield c
        for j in range(k):
            d=circuits[j]
            for i in indices(c&d):
                mask=(c|d)^(1<<i)
                if any(not q&~mask for q in circuits):
                    continue
                q=fundamental(cols,mask)[0]
                circuits.append(q)
        k+=1


def scalar_cells(columns,tag,allowed):
    sites=list(indices(allowed))
    # Place the vertical in its own bit even if ambient private rows are redundant.
    vertical=1<<max((columns[j].bit_length() for j in sites),default=0)
    lifted=[columns[j]|(vertical if tag>>j&1 else 0) for j in sites]+[vertical]
    dual_rows=fundamental(lifted,(1<<len(lifted))-1)
    dual=[sum((row>>j&1)<<k for k,row in enumerate(dual_rows)) for j in range(len(lifted))]
    for c in through(dual,len(sites)):
        yield sum(1<<j for k,j in enumerate(sites) if not c>>k&1)


def cells(K,tags,n):
    """Yield maximal simultaneous agree masks of full private rank."""
    full=(1<<n)-1
    if any(not 0<=r<=full for r in (*K,*tags)):
        raise ValueError("invalid private/tag row")
    columns=[sum((r>>i&1)<<k for k,r in enumerate(K)) for i in range(n)]
    def visit(available,depth):
        if depth==len(tags):
            yield available
        else:
            for cell in scalar_cells(columns,tags[depth],available):
                yield from visit(cell,depth+1)
    yield from visit(full,0)


def tag_lifts(K,tags,n):
    """Yield (cell, predicted global tag rows), canonical on the private span."""
    K,tags=tuple(K),tuple(tags)
    for mask in cells(K,tags,n):
        pivots={}
        for row in K:
            v,full=row&mask,row
            while v:
                k=v.bit_length()-1
                if k not in pivots:
                    pivots[k]=v,full
                    break
                v0,x=pivots[k]
                v,full=v^v0,full^x
        predictions=[]
        agree=(1<<n)-1
        for tag in tags:
            v=tag&mask
            full=0
            while v:
                a,x=pivots[v.bit_length()-1]
                v,full=v^a,full^x
            predictions.append(full)
            agree &= ~(tag^full)
        if agree!=mask:
            raise ArithmeticError("tag lift failed original agreement replay")
        yield mask,tuple(predictions)


def query(K,tags,omega):
    K,tags,omega=tuple(K),tuple(tags),tuple(omega)
    n=len(omega)
    if any(not 0<=row<1<<n or row>>i&1 for i,row in enumerate(omega)) or any(
            (omega[i]>>j ^ omega[j]>>i)&1 for i,j in combinations(range(n),2)):
        raise ValueError("invalid alternating matrix")
    rank=len(independent(K))
    for mask in cells(K,tags,n):
        for i,j in combinations(indices(mask),2):
            result=anchored(K,tags,omega,mask,i,j)
            if result is not None:
                ok,(S,x,y)=result
                if not ok or S.bit_count()!=rank+2 or S&~mask:
                    raise ArithmeticError("physical lifted witness failed")
                return "SAT",(S,x,y)
    return "NO",None


if __name__=="__main__":
    from random import Random
    rng=Random(992)
    for trial in range(160):
        n=rng.randrange(1,9)
        K=tuple(independent(rng.randrange(1<<n) for _ in range(rng.randrange(5))))
        tags=tuple(rng.randrange(1<<n) for _ in range(2))
        full=(1<<n)-1
        rowspace={0}
        for r in K:
            rowspace|={s^r for s in rowspace}
        expected={full&~(a^tags[0])&~(b^tags[1]) for a in rowspace for b in rowspace}
        expected={m for m in expected if len(independent(k&m for k in K))==len(K)}
        seen=[m for m,_ in tag_lifts(K,tags,n)]
        assert len(seen)==len(set(seen)) and set(seen)==expected
        omega=[0]*n
        for i,j in combinations(range(n),2):
            if rng.getrandbits(1):
                omega[i]|=1<<j
                omega[j]|=1<<i
        def live(mask):
            rel=[x for x in range(1<<n) if not x&~mask and all(not (x&r).bit_count()%2 for r in K)]
            def pair(x,y):
                return sum((omega[i]&y).bit_count() for i in indices(x))%2
            return any(pair(x,y) for x,y in combinations(rel,2))
        assert (query(K,tags,omega)[0]=="SAT")==any(live(m) for m in expected)
    # Unbounded rank, one scalar and joint lift despite 2^rank private functionals.
    n=140
    K=[3<<(2*i) for i in range(n//2)]
    assert list(cells(K,[sum(K),0],n))==[(1<<n)-1]
    print("160 exact cell families and physical decisions; rank-70 singleton output")
