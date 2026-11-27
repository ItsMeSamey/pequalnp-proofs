"""Independent GF(4) support polynomial tests inside GF(16)=F2[z]/(z^4+z+1)."""
from itertools import combinations_with_replacement, product
from random import Random


def multiply(a,b):
    out=0
    while b:
        if b&1:out^=a
        b>>=1
        a<<=1
        if a&16:a^=19
    return out


times=[[multiply(a,b) for b in range(16)] for a in range(16)]
inverse=[None]+[next(b for b in range(1,16) if times[a][b]==1) for a in range(1,16)]
omega=6
base=(0,1,omega,omega^1)
assert times[omega][omega]==omega^1


def determinant(matrix):
    rows=[r.copy() for r in matrix]
    det=1
    for i in range(len(rows)):
        pivot=next((k for k in range(i,len(rows)) if rows[k][i]),None)
        if pivot is None:return 0
        rows[i],rows[pivot]=rows[pivot],rows[i]
        p=rows[i][i]
        det=times[det][p]
        for k in range(i+1,len(rows)):
            w=times[rows[k][i]][inverse[p]]
            for j in range(i,len(rows)):
                rows[k][j]^=times[w][rows[i][j]]
    return det


def pfaffian(M):
    # Independent matching recurrence only for bounded test dimensions.
    if not M:return 1
    ans=0
    for j in range(1,len(M)):
        if M[0][j]:
            sub=[[v for k,v in enumerate(row) if k not in (0,j)]
                 for i,row in enumerate(M) if i not in (0,j)]
            ans^=times[M[0][j]][pfaffian(sub)]
    return ans


def block(J,X,odd):
    n=len(J)
    m=n+int(odd)
    M=[[0]*(2*m) for _ in range(2*m)]
    weights=X+[1] if odd else X
    for i in range(m):
        if i<n:M[i][i+m]=M[i+m][i]=1
        for j in range(i+1,m):
            b=J[i][i] if j==n else times[J[i][j]][J[i][j]]^times[J[i][i]][J[j][j]]
            M[i][j]=M[j][i]=b
            c=times[times[b][b]][times[weights[i]][weights[j]]]
            M[i+m][j+m]=M[j+m][i+m]=c
    return pfaffian(M)


def minors(J):
    n=len(J)
    result=[]
    for mask in range(1<<n):
        I=[j for j in range(n) if mask>>j&1]
        result.append(determinant([[J[i][j] for j in I] for i in I]))
    return result


def polynomial(J,X):
    even=odd=0
    for s,v in enumerate(minors(J)):
        if v:
            w=1
            for i,x in enumerate(X):
                if s>>i&1:w=times[w][x]
            if s.bit_count()%2:odd^=w
            else:even^=w
    assert (even,odd)==(block(J,X,False),block(J,X,True))


def mixed(H,a,b):
    n=len(H)
    K=[[v^(omega if b>>i&b>>j&1 else 0) for j,v in enumerate(row)] for i,row in enumerate(H)]
    original=minors(K)
    witnesses=[x for x in range(1<<n) if (x&a).bit_count()%2==1 and (x&b).bit_count()%2==0
               and all(not(x>>i&1) or sum(H[i][j] for j in range(n) if x>>j&1)%2==0 for i in range(n))]
    losses={}
    for t in (1,omega,omega^1,2):
        updated=minors([[v^(t if a>>i&a>>j&1 else 0) for j,v in enumerate(row)] for i,row in enumerate(K)])
        gained=[s for s,v in enumerate(updated) if v and not original[s]]
        lost=[s for s,v in enumerate(updated) if not v and original[s]]
        assert bool(gained)==bool(witnesses)
        if t not in base:assert not lost
        losses[t]=lost
    return losses


if __name__=='__main__':
    rng=Random(4953)
    for n in range(5):
        for _ in range(16):
            J=[[0]*n for i in range(n)]
            for i,j in combinations_with_replacement(range(n),2):J[i][j]=J[j][i]=rng.choice(base)
            for domain in (base,range(16)):polynomial(J,[rng.choice(domain) for i in range(n)])
    for n in (1,2,3):
        pairs=list(combinations_with_replacement(range(n),2))
        for code in range(1<<len(pairs)):
            H=[[0]*n for i in range(n)]
            for k,(i,j) in enumerate(pairs):H[i][j]=H[j][i]=code>>k&1
            for a,b in product(range(1<<n),repeat=2):mixed(H,a,b)
    losses=mixed([[1,0],[0,0]],3,2)
    assert losses=={1:[1],omega:[2],omega^1:[3],2:[]}
    print('160 polynomial evaluations; all binary symmetric H and all readouts through n=3; NO losses',losses)
