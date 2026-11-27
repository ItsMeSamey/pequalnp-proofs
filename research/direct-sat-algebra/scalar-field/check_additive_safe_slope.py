from itertools import product
from random import Random
from affine_binomial import power
from punctured_witness import BinaryField
from additive_safe_slope import find,moment


class F2(BinaryField):
    def __init__(self):
        self.m,self.size,self.modulus,self.trace_mask=1,2,3,1


def check():
    rng=Random(913)
    maps=0
    moments=0
    for f in (F2(),BinaryField(7),BinaryField(11),BinaryField(19),BinaryField(37)):
        q,m=f.size,f.m
        cases=(product(range(q),repeat=m) if q<=8 else
               [tuple(rng.randrange(q) for _ in range(m)) for _ in range(24)])
        for a in cases:
            forbidden=set()
            for x in range(1,q):
                y=0
                for j,c in enumerate(a):
                    y ^= f.mul(c,power(f,x,1<<j))
                forbidden.add(f.mul(y,f.inverse(x)))
            good=set(range(q))-forbidden
            assert len(good)%2 and find(f,a) in good
            for t in list(range(q))+[q+2,2*q-2]:
                expected=0
                for s in good: expected ^= power(f,s,t)
                assert moment(f,a,t)==expected,(q,a,t)
                moments+=1
            maps+=1
    print(maps,"maps and",moments,"moments passed, including all maps on F2, F4, F8")


if __name__=="__main__":
    check()
