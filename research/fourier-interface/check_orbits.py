"""Cross-check a literal Walsh construction against the positive-binomial formula."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod

def binom(n,k):
    return F(prod(n-i for i in range(k)),factorial(k))

def sign(mask,x):
    return (-1)**((mask&x).bit_count())

def run(b,R,A):
    j=1 if not R%2 else 2
    q=b-j-1
    chosen=(1<<(j+1))-2
    free_mask=((1<<b)-1) ^ ((1<<(j+1))-1)
    d=R-1
    fs=[(-1)**A*sum((-2)**h*binom(x.bit_count()-A,h) for h in range(R))
        for x in range(1<<b)]
    # Align the output by the full swap. The remaining convolution is f(W).
    mh=[sum(fs[x]*sign(mask,x) for x in range(1<<b))/(1<<b) for mask in range(1<<b)]
    weights=[F(i,i+1) for i in range(b)]
    eligible=[mask for mask in range(1<<b) if mask&((1<<(j+1))-1)==chosen]
    kernel=[mh[mask]*prod(weights[i] for i in range(b) if mask>>i&1) for mask in eligible]
    free_range=range(q)
    for eps in range(1<<q):
        observed=sum(k*sign(eps,mask>>(j+1)) for mask,k in zip(eligible,kernel))
        total=0
        for u in range(1<<q):
            chance=prod((1+weights[p+j+1]*(-1)**(((u^eps)>>p)&1))/2 for p in free_range)
            total+=chance*binom(u.bit_count()-A,d-j)
        expected=(-1)**A*(-2)**d*F((-1)**j,2**j)*prod(weights[1:j+1])*total
        assert observed==expected and observed!=0,(b,R,A,eps,observed,expected)
    # The image of restricted exceptional rows is exactly the complementary weight set.
    restricted={x>>(j+1) for x in range(1<<b) if not A<=x.bit_count()<A+R}
    kernel_size=sum(comb(q,w) for w in range(q+1) if A<=w and w+j+1<A+R)
    assert kernel_size==(1<<q)-len(restricted)
    return 1<<q

if __name__=='__main__':
    configurations=0
    eigenvalues=0
    for b in range(3,8):
        for R in range(2,b+1):
            for A in range(0,b-R+2):
                configurations+=1
                eigenvalues+=run(b,R,A)
    print(f'{configurations} orbit configurations, {eigenvalues} exact rational eigenvalues and all restricted-kernel dimensions matched.')
