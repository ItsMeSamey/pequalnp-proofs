"""Lift a proposed full-rank or redundant list to exact Gaussian-rational weights."""
from fractions import Fraction as F
from search_rows import search

def add(a,b):
    return a[0]+b[0],a[1]+b[1]
def prod(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def negative(a):
    return -a[0],-a[1]
def inverse(a):
    den=a[0]*a[0]+a[1]*a[1]
    return a[0]/den,-a[1]/den
Z=(F(0),F(0))
entries=[(F(1),F(0)),(F(0),F(1)),(F(-1),F(0)),(F(0),F(-1)),Z]
def lift(cols,target):
    rows=[[entries[c[x]] for c in cols]+[(F(y),F(0))] for x,y in enumerate(target)]
    basis={}
    for row in rows:
        row=list(row)
        for j,p in sorted(basis.items()):
            factor=negative(row[j])
            row=[add(v,prod(factor,w)) for v,w in zip(row,p)]
        j=next((k for k,v in enumerate(row[:-1]) if v!=Z),None)
        if j is None:
            if row[-1]!=Z:return None
        else:
            inv=inverse(row[j]);basis[j]=[prod(inv,v) for v in row]
    sol=[Z]*len(cols)
    for j,row in sorted(basis.items(),reverse=True):
        y=row[-1]
        for v,c in zip(row[:-1],sol):y=add(y,negative(prod(v,c)))
        sol[j]=y
    for row in rows:
        s=Z
        for a,c in zip(row[:-1],sol):s=add(s,prod(a,c))
        assert s==row[-1]
    return sol
if __name__=='__main__':
    g=[1]*7+[-1]
    status,cols,nodes=search(3,g,2,5000)
    assert status=='SAT' and lift(cols,g) is not None
    target=[(-1)**sum(((x>>(3*i))&7)==7 for i in range(3)) for x in range(512)]
    cols=[{x:0 if all((x>>(3*i))&7==7 for i in range(3) if m>>i&1) else -1 for x in range(512)} for m in range(8)]
    assert lift(cols,target)==[(F((-2)**m.bit_count()),F(0)) for m in range(8)]
    print('verified 8-row search and 512-row product lifts')
