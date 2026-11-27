"""Integer sign-character computation of binary determinant parity on syndrome fibers."""
from quadratic_target import insert,reduce_vector


def determinant(mat):
    n=len(mat)
    if not n: return 1
    a=[row[:] for row in mat]
    prev=sign=1
    for j in range(n-1):
        i=next((i for i in range(j,n) if a[i][j]),None)
        if i is None: return 0
        if i!=j:
            a[i],a[j]=a[j],a[i]
            sign=-sign
        pivot=a[j][j]
        for i in range(j+1,n):
            for k in range(j+1,n):
                num=a[i][k]*pivot-a[i][j]*a[j][k]
                a[i][k]=num//prev
        prev=pivot
    return sign*a[-1][-1]


def parity(n,syndrome_rows,matrix_at,*,fixed=0,values=0,pins=()):
    """matrix_at(Ht) gives a binary matrix D; compute det(D+diag(t)) parity.

    syndrome_rows and pin rows are n-bit masks. fixed,values specify coordinate pins.
    """
    if n<0 or not 0<=fixed<1<<n or not 0<=values<1<<n or values&~fixed:
        raise ValueError("invalid fixed assignment")
    syndrome_rows=tuple(syndrome_rows)
    if any(not 0<=v<1<<n for v in syndrome_rows): raise ValueError("invalid syndrome row")
    basis=[]
    echelon={}
    def add(v):
        rem,key=reduce_vector(v,echelon)
        if not rem: return key,False
        key=1<<len(basis)
        basis.append(v)
        insert(v,key,echelon)
        return key,True
    pin_goal=0
    for v,b in pins:
        if not 0<=v<1<<n or b not in (0,1): raise ValueError("invalid pin")
        b^=(v&values).bit_count()&1
        key,new=add(v&~fixed)
        if new:
            if b: pin_goal|=key
        elif (key&pin_goal).bit_count()%2!=b:
            return 0
    p=len(basis)
    checks=[add(v&~fixed)[0] for v in syndrome_rows]
    shift=sum(((v&values).bit_count()%2)<<j for j,v in enumerate(syndrome_rows))
    r=len(basis)
    columns=[sum(((v>>i)&1)<<j for j,v in enumerate(basis)) for i in range(n)]
    result=0
    for high in range(1<<(r-p)):
        word=pin_goal|(high<<p)
        target=shift^sum(((key&word).bit_count()%2)<<j for j,key in enumerate(checks))
        D=matrix_at(target)
        if len(D)!=n or any(len(row)!=n or any(v not in (0,1) for v in row) for row in D):
            raise ValueError("invalid binary matrix oracle")
        total=0
        for char in range(1<<r):
            M=[]
            for i,row in enumerate(D):
                if fixed>>i&1:
                    new=list(row)
                    new[i]^=(values>>i)&1
                else:
                    sign=-1 if (char&columns[i]).bit_count()%2 else 1
                    new=[(1+sign)*c for c in row]
                    new[i]=row[i]+sign*(1-row[i])
                M.append(new)
            val=determinant(M)
            total+=-val if (char&word).bit_count()%2 else val
        if total%(1<<r): raise ArithmeticError("inexact character inversion")
        result^=(total>>r)&1
    return result
