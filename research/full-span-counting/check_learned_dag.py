#!/usr/bin/env python3
"""Check weighted prefix contraction when predictors are correct only on valid traces."""
from fractions import Fraction as F
from itertools import product
from random import Random


def holds(x,pos,neg):
    return x & pos == pos and not x & neg


def truth(x):
    # Three raw cubes share positive/negative input pins across gates.
    a=holds(x,1,2)
    b=holds(x,1,4)
    c=holds(x,8,2)
    return [int(a or b),int(b!=c)]


def correct(x):
    a,b=truth(x)
    g=int(bool(a and not b))
    return a,b,g,int(bool(g or (a and b)))


def guesses(x,y):
    a,b,g,h=correct(x)
    if not (x&3):
        a=F(7,11)
    # Raw input predicates may appear in any gate, and all dependencies point back.
    wrong=2**161+13
    p1=F(b)+F(wrong,3)*(y[0]-a)
    p2=F(g)-F(wrong,5)*((y[0]-a)+4*(y[1]-b))
    p3=F(h)+F(wrong,7)*((y[2]-g)-3*(y[0]-a))
    return a,p1,p2,p3


def main():
    rng=Random(6926)
    core=lambda x: bool(x&3) and not holds(x,12,0)
    requests=0
    negative=0
    for length in range(5):
        compiled={}
        for x in range(16):
            if not core(x):
                continue
            for y in product((0,1),repeat=length):
                val=1
                padded=y+(0,)*(4-length)
                for wire,pred in zip(y,guesses(x,padded)):
                    row=1-wire-pred+2*wire*pred
                    negative+=row<0
                    val*=row
                assert val==int(y==correct(x)[:length])
                compiled[x,y]=val
        choices=list(product((-1,0,1),repeat=length))
        for yp in choices:
            for xp in rng.sample(list(product((-1,0,1),repeat=4)),7):
                def selected(bits,pins):
                    return all(p==-1 or b==p for b,p in zip(bits,pins))
                wanted=lambda x: selected(tuple((x>>i)&1 for i in range(4)),xp)
                total=sum(v for (x,y),v in compiled.items() if wanted(x) and selected(y,yp))
                brute=sum(core(x) and wanted(x) and selected(correct(x)[:length],yp) for x in range(16))
                assert total==brute
                requests+=1
    assert negative>0
    print(f"All five prefixes matched pointwise; {requests} joint wire/input pin sums passed with {negative} negative local factors.")


if __name__=='__main__':
    main()
