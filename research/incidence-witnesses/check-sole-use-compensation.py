from fractions import Fraction as F
from math import comb
N=161203
L=646425
eps=N*F(sum(comb(402,i) for i in range(138)),2**402)
cost=L-4*N+1+F(3*N,139)+(L-1)*eps
assert F(149,2)*68<=cost<F(149,2)*69
bilateral=L-4*N+1+F(2*N,139)+2*(L-1)*eps+F(2*N,2**403)
for scale,threshold in ((2,7903),(4,15805),(8,31609),(16,63217)):
    assert F(threshold-1,scale)<=bilateral<F(threshold,scale)
print('One-sided 69 and four bilateral motif thresholds passed')
