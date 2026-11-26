"""All-boundary minima of an additive, sparse signed Walsh score over binary pins.

A signed frequency or boundary is (mask, offset); a score term is
(weight, mask, offset). Returns {original_boundary_word: (minimum, witness)}.
Inconsistent hard pins give an empty table. Unattainable boundaries are absent.
"""
from fractions import Fraction
from affine_cell_energy import dot, solve


def echelon(vectors):
    basis = {}
    for v in vectors:
        while v:
            i = v.bit_length()-1
            if i not in basis:
                basis[i]=v
                break
            v ^= basis[i]
    return basis


def contains(basis,v):
    while v:
        i=v.bit_length()-1
        if i not in basis:
            return False
        v ^= basis[i]
    return True


def combine(bits, vectors):
    out=0
    for i,v in enumerate(vectors):
        if bits>>i&1: out ^= v
    return out


def images(x, rows):
    return sum(dot(x,row)<<i for i,row in enumerate(rows))


def transpose(rows,n):
    return [sum((row>>i&1)<<j for j,row in enumerate(rows)) for i in range(n)]


def minimum_table(n, terms, boundaries=(), pins=(), constant=0):
    pins=tuple(pins); boundaries=tuple(boundaries); terms=tuple(terms)
    for mask,offset in boundaries+tuple((a,b) for _,a,b in terms):
        if not 0<=mask<1<<n or offset not in (0,1): raise ValueError("bad affine form")
    if not all(isinstance(weight,(int,Fraction)) for weight in (constant,*(w for w,_,_ in terms))):
        raise ValueError("use exact rational weights")
    chart=solve(n,pins)
    if chart is None:return {},()
    origin,free=chart
    def param(a,b):
        return images(a,free), b^dot(a,origin)
    grouped={}
    for w,a,b in terms:
        f,b=param(a,b)
        grouped[f]=grouped.get(f,0)+(w if not b else -w)
    constant+=grouped.pop(0,0)
    A=[f for f in sorted(grouped) if grouped[f]]
    s=len(A); k=len(free)
    fields=[param(a,b) for a,b in boundaries]
    B=[f for f,b in fields]
    offset=sum(b<<i for i,(_,b) in enumerate(fields))
    AT=transpose(A,k)
    _,H=solve(s,((a,0) for a in AT))
    _,null_A=solve(k,((a,0) for a in A))
    invisible=[images(v,B) for v in null_A]
    _,tests=solve(len(B),((v,0) for v in invisible))
    # Retain independent nonzero visible boundary functionals modulo aliases.
    checks=[]; D=[]; seen={}
    for c in tests:
        f=combine(c,B)
        if contains(seen,f):continue
        seen=echelon([*seen.values(),f])
        d,_=solve(s,((a,f>>i&1) for i,a in enumerate(AT)))
        D.append(d); checks.append(c)
    columns=transpose([*H,*D],s)
    virtual=[1<<(len(H)+j) for j in range(len(D))]
    suffix=[None]*(s+1)
    suffix[s]=echelon(virtual)
    for j in range(s-1,-1,-1):
        suffix[j]=echelon([*suffix[j+1].values(),columns[j]])
    dp={0:(constant,0)}
    sizes=[1]
    for j,column in enumerate(columns):
        nxt={}
        for t,(value,y) in dp.items():
            for bit in (0,1):
                u=t^(column if bit else 0)
                if not contains(suffix[j+1],u):continue
                cost=value+(grouped[A[j]] if not bit else -grouped[A[j]])
                if u not in nxt or cost<nxt[u][0]:
                    nxt[u]=(cost,y|(bit<<j))
        dp=nxt
        sizes.append(len(dp))
    # Enumerate the attainable original boundaries, including affine offsets
    # and directions independent of A. Produce an original-coordinate witness.
    B_basis=list(echelon(transpose(B,k)).values())
    out={}
    for b_index in range(1<<len(B_basis)):
        b=combine(b_index,B_basis)
        target=images(b,checks)<<len(H)
        cost,y=dp[target]
        eq=[(a,y>>j&1) for j,a in enumerate(A)]+[(a,b>>j&1) for j,a in enumerate(B)]
        seed,_=solve(k,eq)
        out[b^offset]=cost,origin^combine(seed,free)
    return out,tuple(sizes)


def nae_minimum_table(n, triples, boundaries=(), pins=()):
    """Each triple is three affine (mask,offset) literals; count violated gates."""
    terms=[]; length=0
    for triple in triples:
        triple=tuple(triple)
        if len(triple)!=3:raise ValueError("NAE requires three affine literals")
        if any(not 0<=a<1<<n or b not in (0,1) for a,b in triple):
            raise ValueError("bad affine literal")
        length+=1
        for i,j in ((0,1),(0,2),(1,2)):
            a,b=triple[i]; c,d=triple[j]
            terms.append((Fraction(1,4),a^c,b^d))
    return minimum_table(n,terms,boundaries,pins,Fraction(length,4))
