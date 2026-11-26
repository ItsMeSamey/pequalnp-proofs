"""Independently verify two structured lower bounds for polynomial selectors."""
from itertools import product
from connected_hole import connected, flux, rank
from separator_degree import certificate

E=[16,20,17,23,32,40,33,45,64,73,128,129]
assert [certificate(E,8,2,k) for k in range(4)]==[False,False,False,True]
for x in range(16):
    x1,x2,x3,x4=[x>>i&1 for i in range(4)]
    c=2+4*x1+8*x1*x2+64*x1*x2*x3
    assert all((e&c).bit_count()%2==0 or (e&(1+(x<<4))).bit_count()%2 for e in E)
assert flux(E,8)==set(range(0,16,2))-{2}

def chain(n):
    # Potentials are gauged at L. The U,D coordinates both evaluate to one
    # under lambda=bit zero. Distinct vertex incidence vectors have XOR edge.
    L,R,O,U,D=0,2,4,1,9
    X=[1<<(4+i) for i in range(n)]
    y,z,w=[1<<(4+n+i) for i in range(3)]
    edges=([(L,v) for v in X]+[(R,v) for v in X]+list(zip(X,X[1:]))+
           [(X[-1],D),(U,y),(U,z),(y,X[0]),(z,X[0]),(L,y),(y,O),(R,z),(z,O),
            (D,w),(w,R),(w,X[-1])])
    return [u^v for u,v in edges]

for n in range(1,6):
    C=chain(n)
    assert rank(C)==n+7 and connected(C) and connected([e>>4 for e in C])
    assert flux(C,n+7)==set(range(0,16,2))-{10}
    if n<=4:
        assert not certificate(C,n+7,10,n-1)
print("Cubic instance and patched graphic family n=1,...,5 passed")
