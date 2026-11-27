"""Physical indexed alternating queries. SAT/NO witnesses refer to true supports.

The automatic-tag and forced-zero-coordinate reductions are exact. In general
incompatible relaxed candidates leave UNKNOWN; a relaxed impossibility is NO.
K and tags are row masks; omega is packed alternating rows. Physical indices
are never relabeled in the returned support and relation words.
"""
from itertools import combinations
from gim_binary_parity import solve as delta_parity
from hidden_product_network import encoder
from quadratic_centroid import independent
from quadratic_target import apply_basis,reduce_vector,insert


def indices(word):
    while word:
        b=word&-word
        yield b.bit_length()-1
        word^=b


def anchored(K,tags,omega,allowed,i,j):
    n=len(omega)
    K=independent(k&allowed for k in K)
    r=len(K)
    B=(*K,1<<i,1<<j)
    sites=list(indices(allowed))
    bcols=[sum(((a>>s)&1)<<k for k,a in enumerate(B)) for s in sites]
    pivots={}
    chosen=[k for k,b in enumerate(bcols) if insert(b,0,pivots)]
    if len(chosen)!=r+2:
        return None
    decode=encoder([bcols[k] for k in chosen])
    N=r+len(sites)
    rows=[0]*(2*N)
    def edge(a,b):
        rows[a]|=1<<b
        rows[b]|=1<<a
    basis=set(chosen)
    twist=sum(1<<(2*k) for k in range(r))
    for k,s in enumerate(sites):
        a=r+k
        if k in basis:
            twist|=1<<(2*a)
        else:
            for h in indices(decode(bcols[k])):
                edge(2*a,2*(r+chosen[h]))
        for h,row in enumerate(K):
            if row>>s&1:
                edge(2*h+1,2*a+1)
        for l in range(k):
            if omega[s]>>sites[l]&1:
                edge(2*a+1,2*(r+l)+1)
    result=delta_parity(rows,twist)
    if result is None:
        return None
    sel=[k for k in range(len(sites)) if result>>(2*(r+k))&1]
    if len(sel)!=r+2:
        raise ArithmeticError("wrong physical basis size")
    decoder=encoder([bcols[k] for k in sel])
    frame=[1<<sites[k] for k in sel]
    x,y=[apply_basis(frame,decoder(1<<h)) for h in (r,r+1)]
    S=sum(frame)
    if any((row&v).bit_count()%2 for row in K for v in (x,y)) or not (apply_basis(omega,x)&y).bit_count()%2:
        raise ArithmeticError("physical private or alternating replay failed")
    ok=not any((row&v).bit_count()%2 for row in tags for v in (x,y))
    return ok,(S,x,y)


def query(K,tags,omega):
    omega=tuple(omega)
    n=len(omega)
    full=(1<<n)-1
    K,tags=tuple(K),tuple(tags)
    if any(not 0<=a<=full for a in (*K,*tags,*omega)) or any(a>>i&1 for i,a in enumerate(omega)) or any(
            ((omega[i]>>j)^(omega[j]>>i))&1 for i,j in combinations(range(n),2)):
        raise ValueError("invalid packed physical instance")
    allowed=full
    while True:
        priv={}
        for k in K:
            insert(k&allowed,0,priv)
        relevant=[reduce_vector(row&allowed,priv)[0] for row in tags]
        if not any(relevant):
            break
        allrows=priv.copy()
        for row in relevant:
            insert(row,0,allrows)
        drop=0
        for s in indices(allowed):
            e=1<<s
            if reduce_vector(e,priv)[0] and not reduce_vector(e,allrows)[0]:
                drop|=e
        if not drop:
            break
        allowed^=drop
    unknown=False
    for i,j in combinations(indices(allowed),2):
        answer=anchored(K,tags,omega,allowed,i,j)
        if answer is None:
            continue
        ok,w=answer
        if ok:
            # Extend the private column span to ambient rank. Every extra column
            # is independent over those retained, so x,y remain the full kernel.
            S,x,y=w
            cols=[sum(((row>>s)&1)<<k for k,row in enumerate(K)) for s in range(n)]
            span={}
            for s in indices(S):
                insert(cols[s],0,span)
            for s in indices(full^S):
                if insert(cols[s],0,span):
                    S|=1<<s
            if S.bit_count()!=len(independent(K))+2:
                raise ArithmeticError("square physical extension failed")
            return 'SAT',(S,x,y)
        unknown=True
    return ('UNKNOWN' if unknown else 'NO'),None
