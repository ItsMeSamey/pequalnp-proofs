"""Verify the exact flow identity including semantic OR edits, and q401 thresholds."""
from fractions import Fraction as F
from itertools import product
from random import Random

rng = Random(81931)
count = 0
for _ in range(200):
    gates = [(rng.choice(('OR','AND')), rng.randrange(j), rng.randrange(j))
             for j in range(4,14)]
    fanout = [0]*14
    for op,left,right in gates:
        fanout[left] += 1
        fanout[right] += 1
    for raw in product((0,1),repeat=4):
        wire = list(raw)
        actual = and_one = correction = 0
        for op,left,right in gates:
            zero = 2-wire[left]-wire[right]
            edited = op == 'OR' and rng.randrange(4) == 0
            actual += bool(edited or zero)
            and_one += op == 'AND' and zero == 1
            correction += (1-zero) if edited else 0
            wire.append(int(edited or (zero<2 if op=='OR' else zero==0)))
        source = sum(fanout[i] for i in range(4) if not raw[i])
        internal = sum(fanout[i]-1 for i in range(4,14) if not wire[i])
        assert actual == source+internal+and_one+correction
        count += 1

q=401
n=q*q+q+1
for h in (80,203):
    d=h*(q+1)+1
    p=F(d,n)
    v=2*(n-d)
    k=q+1-h
    target=646425-(2*v-1-2*v//(k+1))-4*d
    edges=1+2*h*(q+1)+h*h*q
    same=F(d*(d-1),n*(n-1))
    j=max(same,F(edges,n*(q+1)),F(d*d-edges,n*(n-q-1)))
    unit=p-2*j-same/2 if h==80 else 2*(p-j)
    threshold=32638 if h==80 else 6443
    assert (threshold-1)*unit<target<=threshold*unit
print(count,'circuit restrictions and exact thresholds passed')
from math import comb
epsilon = 2*n*F(sum(comb(402,i) for i in range(138)),2**402)
bound = 646425-4*n+1+F(2*n,139)+646424*epsilon
assert F(63216,16) <= bound < F(63217,16)
print('independent OR-parent certificate threshold passed')
assert F(15804,4)<=bound<F(15805,4)
assert F(31608,8)<=bound<F(31609,8)
