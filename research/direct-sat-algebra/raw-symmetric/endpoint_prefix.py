"""Endpoint-local matching marginals, optionally conditioned on a shared syndrome."""
from fractions import Fraction
from itertools import combinations,product
from quadratic_centroid import independent
from quadratic_target import apply_basis,insert,reduce_vector
from hidden_product_network import encoder


def _pfaffian(matrix):
    a=[[Fraction(x) for x in row] for row in matrix]
    n=len(a)
    value=1
    for k in range(0,n,2):
        j=next((j for j in range(k+1,n) if a[k][j]),None)
        if j is None: return 0
        if j!=k+1:
            a[k+1],a[j]=a[j],a[k+1]
            for row in a: row[k+1],row[j]=row[j],row[k+1]
            value=-value
        p=a[k][k+1]
        value*=p
        for i in range(k+2,n):
            for j in range(i+1,n):
                a[i][j]-=(a[k][i]*a[k+1][j]-a[k][j]*a[k+1][i])/p
                a[j][i]=-a[i][j]
    value=Fraction(value)
    if value.denominator!=1: raise ArithmeticError("nonintegral Pfaffian")
    return value.numerator


def _marginals(n,local,d,choices,signs):
    loops=[sum(signs[i]**x * (x^((d>>i)&1)) for x in choices[i]) for i in range(n)]
    edges={(i,j):sum(signs[i]**x*signs[j]**y*local(i,j,x,y)
                     for x,y in product(choices[i],choices[j])) for i,j in combinations(range(n),2)}
    return loops,edges


def _weighted(n,loops,edges):
    a=[[0]*(2*n) for _ in range(2*n)]
    def edge(i,j,v):
        a[i][j]=v
        a[j][i]=-v
    for (i,j),v in edges.items():
        edge(i,j,v)
        edge(i+n,j+n,1)
    for i,v in enumerate(loops): edge(i,i+n,v)
    return _pfaffian(a)


def parity(n,H,edge_value,*,offset=0,fixed=0,values=0,pins=()):
    """edge_value(u,i,j,t_i,t_j) returns a Boolean matrix entry, i<j, u=Ht.

    All entries are symmetric. The diagonal is t+offset. Pins are (mask,bit).
    """
    if n<0 or not 0<=offset<1<<n or not 0<=fixed<1<<n or not 0<=values<1<<n or values&~fixed:
        raise ValueError("invalid control specification")
    H=tuple(H)
    if any(not 0<=v<1<<n for v in H): raise ValueError("invalid syndrome")
    echelon={}
    basis=[]
    def add(v):
        rem,code=reduce_vector(v,echelon)
        if not rem: return code,False
        code=1<<len(basis)
        basis.append(v)
        insert(v,code,echelon)
        return code,True
    pin_goal=0
    for v,b in pins:
        if not 0<=v<1<<n or b not in (0,1): raise ValueError("invalid pin")
        b^=(v&values).bit_count()%2
        code,new=add(v&~fixed)
        if new: pin_goal|=code*b
        elif (code&pin_goal).bit_count()%2!=b: return 0
    p=len(basis)
    codes=[add(v&~fixed)[0] for v in H]
    shift=sum(((v&values).bit_count()%2)<<j for j,v in enumerate(H))
    r=len(basis)
    cols=[sum(((v>>i)&1)<<j for j,v in enumerate(basis)) for i in range(n)]
    choices=[((values>>i)&1,) if fixed>>i&1 else (0,1) for i in range(n)]
    out=0
    for high in range(1<<(r-p)):
        word=pin_goal|(high<<p)
        u=shift^sum(((v&word).bit_count()%2)<<j for j,v in enumerate(codes))
        local=lambda i,j,x,y:edge_value(u,i,j,x,y)
        if not r:
            loops,edges=_marginals(n,local,offset,choices,[1]*n)
            rows=[(v%2)<<i for i,v in enumerate(loops)]
            for (i,j),v in edges.items():
                rows[i]^=(v%2)<<j
                rows[j]^=(v%2)<<i
            return int(len(independent(rows))==n)
        total=0
        for char in range(1<<r):
            signs=[(-1 if (char&col).bit_count()%2 else 1) for col in cols]
            loops,edges=_marginals(n,local,offset,choices,signs)
            pf=_weighted(n,loops,edges)
            total+=-pf if (word&char).bit_count()%2 else pf
        if total%(1<<r): raise ArithmeticError("inexact sign inversion")
        out^=(total>>r)&1
    return out


def witness(n,H,f,goal,*,offset=0,center=lambda x:0):
    H=tuple(H)
    if not parity(n,H,f,offset=offset): return None
    t=0
    for i in range(n):
        if not parity(n,H,f,offset=offset,fixed=(1<<(i+1))-1,values=t):
            t|=1<<i
    u=sum(((t&v).bit_count()%2)<<j for j,v in enumerate(H))
    cols=[((t^offset)&(1<<i)) for i in range(n)]
    for i,j in combinations(range(n),2):
        v=f(u,i,j,t>>i&1,t>>j&1)
        cols[i]^=v<<j
        cols[j]^=v<<i
    base=center(t)
    y=encoder(cols)(goal^base)
    if apply_basis(cols,y)^base!=goal: raise ArithmeticError("invalid witness")
    return t,y


def affine_chart(n,entries,*,max_rank):
    """Find a shared residual space up to max_rank for affine endpoint entries."""
    if n<0 or type(max_rank) is not int or max_rank<0: raise ValueError("invalid rank bound")
    rows=[]
    for (i,j),(c,v) in entries.items():
        if not 0<=i<j<n or c not in (0,1) or not 0<=v<1<<n: raise ValueError("invalid entry")
        rows.append(((i,j),c,v,tuple(v^(a<<i)^(b<<j) for a in (0,1) for b in (0,1))))

    for bound in range(min(n,max_rank)+1):
        def search(basis,table,start):
            for k in range(start,len(rows)):
                options=rows[k][3]
                if any(not reduce_vector(v,table)[0] for v in options): continue
                if len(basis)==bound: return None
                for v in options:
                    nt=table.copy()
                    insert(v,1<<len(basis),nt)
                    answer=search(basis+(v,),nt,k+1)
                    if answer is not None:return answer
                return None
            return basis,table
        result=search((),{},0)
        if result is None: continue
        basis,table=result
        entries_local={}
        for key,c,original,options in rows:
            i,j=key
            for v in options:
                rest,code=reduce_vector(v,table)
                if not rest:
                    local=original^v
                    entries_local[key]=c,code,(local>>i)&1,(local>>j)&1
                    break
        def oracle(u,i,j,a,b):
            c,code,ai,aj=entries_local.get((i,j),(0,0,0,0))
            return c^((u&code).bit_count()%2)^(ai&a)^(aj&b)
        return basis,oracle
    return None
