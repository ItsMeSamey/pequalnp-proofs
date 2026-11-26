from itertools import product
from random import Random
import sympy as sp
rng=Random(710)
for case in range(12):
    n=5
    pins=[[rng.choice((-1,-1,0,1)) for _ in range(n)] for _ in range(7)]
    coefficients=[rng.randrange(-3,4) for row in pins]
    for i in range(n+1):
        prefix=list(product((0,1),repeat=i))
        suffix=list(product((0,1),repeat=n-i))
        def compatible(bits,pattern):return all(b==p or p==-1 for b,p in zip(bits,pattern))
        V=sp.Matrix([[c*compatible(x,row[:i]) for c,row in zip(coefficients,pins)] for x in prefix])
        U=sp.Matrix([[int(compatible(y,row[i:])) for y in suffix] for row in pins])
        def gram(x,y):
            pairs=list(zip(x[i:],y[i:]))
            return 0 if any(a>=0 and b>=0 and a!=b for a,b in pairs) else 2**sum(a==b==-1 for a,b in pairs)
        G=sp.Matrix([[gram(x,y) for y in pins] for x in pins])
        assert U*U.T==G and (V*U).rank()==(V*G).rank()
print('72 exact signed-prefix flattening ranks and Gram matrices verified')
