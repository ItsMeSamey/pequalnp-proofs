"""Check the pivot formula, every max-A/B chart, and the packet parity identity."""
from itertools import product

def parity(x):
    return x.bit_count() % 2

def border(rows):
    last=0
    ans=[]
    for row in rows:
        row |= parity(row)<<len(rows)
        ans.append(row)
        last ^= row
    return ans+[last]

def column(rows,j):
    return sum(((r>>j)&1)<<i for i,r in enumerate(rows))

def coords(values):
    tab={0:0}
    for i,v in enumerate(values):
        if v in tab:raise AssertionError('basis dependent')
        tab.update({s^v:t|(1<<i) for s,t in list(tab.items())})
    return tab

def test(m):
    core=[sum(int(j%m<i%m or (i%m==j%m and i//m==j//m))<<j for j in range(2*m))
          for i in range(2*m)]
    N=border(core);n=len(N)
    A=[1<<i for i in range(n)]+[(1<<n)-1]
    B=[column(N,j)|(1<<n) for j in range(n)]+[1<<n]
    assert all(parity(v)==0 for v in N)
    assert all(parity(v)==0 for v in (column(N,j) for j in range(n)))
    for i in range(2*m):
        assert sum(parity(core[i]&column(core,j))<<j for j in range(2*m))==1<<i
    for chosen in range(1<<m):
        mask=chosen|(chosen<<m)
        for i in range(2*m):
            if mask>>i&1:
                assert parity(N[i]&mask)==parity(column(N,i)&mask)==1
    charts=0
    for X,Y in ((A,B),(B,A)):
        # Reverse reference omits last B and includes last A in this symmetric
        # index convention only after changing the two reference indices.
        omit,keep=(n,n) if X==A else (n-1,n-1)
        ri=[i for i in range(n+1) if i!=omit]
        cj=[j for j in range(n+1) if j!=keep]
        tab=coords([X[i] for i in ri]+[Y[keep]])
        D=[[0]*(n+1) for _ in X]
        for iidx,i in enumerate(ri):
            for j in cj:D[i][j]=(tab[Y[j]]>>iidx)&1
        if X==A:
            assert [sum(D[i][j]<<j for j in range(n)) for i in range(n)]==N
        else:
            # Pivoting on the full original main block places its old exceptional
            # vertices last, corresponding to original index n rather than n-1.
            assert [sum(D[i][jidx]<<j for j,jidx in enumerate(cj)) for i in ri]==N
        for a,b in product(range(n+1),repeat=2):
            rr=[i for i in range(n+1) if i!=a]
            tab=coords([X[i] for i in rr]+[Y[b]])
            for ii,i in enumerate(rr):
                for j in range(n+1):
                    if j!=b:assert ((tab[Y[j]]>>ii)&1)==(D[i][j]^D[i][b]^D[a][j]^D[a][b])
            charts+=1
    return charts

if __name__=='__main__':
    print(sum(test(m) for m in range(1,5)), 'maximal charts checked')
