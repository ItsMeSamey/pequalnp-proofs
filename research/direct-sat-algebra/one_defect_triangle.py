"""Three-package feasibility for 2-CNF and h independent parity checks."""
from itertools import combinations
from one_defect_clause_closure import solve_clauses
from quadratic_target import parity


def packed_matrix(A,B):
    """Exact integer product by collision-free Kronecker packing of signed dot products."""
    k=len(B)
    if not k:
        return [[] for row in A]
    bound=max((abs(x) for row in A for x in row),default=0)*max((abs(x) for row in B for x in row),default=0)*k
    width=max(2,(2*bound+1).bit_length())
    mask=(1<<width)-1
    rows=[sum(x<<(width*i) for i,x in enumerate(row)) for row in A]
    cols=[sum(x<<(width*(k-1-i)) for i,x in enumerate(col)) for col in zip(*B)]
    # Lower, signed convolution digits can borrow into the middle coefficient.
    # Adding uniform half-radix to each convolution digit prevents every borrow.
    center=1<<(width-1)
    bias=sum(center<<(width*i) for i in range(2*k-1))
    return [[(((a*b+bias)>>(width*(k-1)))&mask)-center for b in cols] for a in rows]


def product_matrix(A,B):
    """Pad rectangular products for a subcubic arithmetic-operation bound."""
    n,k,m=len(A),len(B),len(B[0])
    size=1<<(max(n,k,m)-1).bit_length()
    if size<=16:
        return packed_matrix(A,B)
    def pad(M):
        return [r+[0]*(size-len(r)) for r in M]+[[0]*size for _ in range(size-len(M))]
    def add(X,Y,sign=1):
        return [[a+sign*b for a,b in zip(x,y)] for x,y in zip(X,Y)]
    def split(M):
        l=len(M)//2
        return [r[:l] for r in M[:l]],[r[l:] for r in M[:l]],[r[:l] for r in M[l:]],[r[l:] for r in M[l:]]
    def mul(X,Y):
        if len(X)<=16:
            return packed_matrix(X,Y)
        a,b,c,d=split(X)
        e,f,g,h=split(Y)
        t1=mul(add(a,d),add(e,h))
        t2=mul(add(c,d),e)
        t3=mul(a,add(f,h,-1))
        t4=mul(d,add(g,e,-1))
        t5=mul(add(a,b),h)
        t6=mul(add(c,a,-1),add(e,f))
        t7=mul(add(b,d,-1),add(g,h))
        ul=add(add(add(t1,t4),t5,-1),t7)
        ur=add(t3,t5)
        ll=add(t2,t4)
        lr=add(add(add(t1,t2,-1),t3),t6)
        return [x+y for x,y in zip(ul,ur)]+[x+y for x,y in zip(ll,lr)]
    return [r[:m] for r in mul(pad(A),pad(B))[:n]]


def solve(N,H,checks,target=0):
    h=len(checks)
    H=tuple(H)
    if N<0 or not 0<=target<1<<h or any(not 0<=r<1<<N for r in checks):
        raise ValueError("invalid check system")
    base=solve_clauses(N,H)
    if base is None:
        return None,{}
    target^=sum(parity(base&r)<<j for j,r in enumerate(checks))
    # A closure is its forced flipped coordinates. Feasible unions are exactly
    # unions free of forbidden flip pairs because unary implications are closed.
    closures=set()
    for i in range(N):
        a=2*i+1-(base>>i&1)
        if solve_clauses(N,H,(a,)) is not None:
            closures.add(sum(1<<j for j in range(N) if solve_clauses(N,H,(a,2*j+(base>>j&1))) is None))
    C=sorted(closures)
    def legal(bits):
        y=base^bits
        return all(not(y>>(a//2)&1==a%2 and y>>(b//2)&1==b%2) for a,b in H)
    signatures={}
    for i in range(N):
        anc=sum(1<<j for j,c in enumerate(C) if c>>i&1)
        label=sum((r>>i&1)<<j for j,r in enumerate(checks))
        signatures[anc]=signatures.get(anc,0)^label
    signatures=[(a,v) for a,v in signatures.items() if a and v]
    cap=(h+2)//3
    packages=[]
    for size in range(min(cap,len(C))+1):
        for part in combinations(range(len(C)),size):
            bits=indices=0
            for j in part:
                bits|=C[j]
                indices|=1<<j
            if legal(bits):
                packages.append((indices,bits))
    def count(domains):
        total=0
        for char in range(1<<h):
            active=[a for a,v in signatures if parity(v&char)]
            small=[a for a in active if a.bit_count()<=2]
            large=[a for a in active if a.bit_count()>2]
            for chosen in range(1<<len(large)):
                banned=0
                for j,a in enumerate(large):
                    if chosen>>j&1:
                        banned|=a
                sets=[[p for p in domain if not p[0]&banned] for domain in domains]
                if not all(sets):
                    continue
                def sign(mask):
                    return (-1)**(sum(bool(mask&a) for a in small)%2)
                def edges(X,Y):
                    return [[sign(x|y)*sign(x) if not x&y and legal(cx|cy) else 0
                             for y,cy in Y] for x,cx in X]
                X,Y,Z=sets
                A,B,D=edges(X,Y),edges(Y,Z),edges(Z,X)
                AB=product_matrix(A,B)
                triangle=sum(v*D[j][i] for i,row in enumerate(AB) for j,v in enumerate(row))
                total+=triangle*((-1)**(parity(char&target)+len(large)-chosen.bit_count()))*(1<<chosen.bit_count())
        value,rem=divmod(total,1<<h)
        assert not rem and value>=0
        return value
    ds=[packages]*3
    ways=count(ds)
    stats=dict(packages=len(packages),large=sum(a.bit_count()>2 for a,_ in signatures),tuples=ways)
    if not ways:
        return None,stats
    for j in range(3):
        while len(ds[j])>1:
            mid=len(ds[j])//2
            trial=ds.copy()
            trial[j]=ds[j][:mid]
            ds[j]=trial[j] if count(trial) else ds[j][mid:]
    y=base^(ds[0][0][1]|ds[1][0][1]|ds[2][0][1])
    return y,stats
