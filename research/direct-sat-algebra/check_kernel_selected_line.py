from itertools import combinations
from random import Random
from punctured_witness import BinaryField
from hidden_product_network import encoder
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import _center,subfield_basis
from paired_coset_parity import parity,find_columns
from additive_slope_prefix import dickson
from product_slack import linearized


def audit(mod):
    f=BinaryField(mod)
    d=f.m
    gram=[f.trace_row(1<<i) for i in range(d)]
    dual=encoder(gram)
    basis=subfield_basis(f)
    L=[apply_basis(basis,j) for j in range(1,1<<len(basis))]
    lines=[0]+[sum(1<<f.mul(f.inverse(f.mul(x,x)),l) for l in L) for x in range(1,f.size)]
    generators=[]
    for i,j in combinations(range(d),2):
        cols=[0]*d
        cols[i]=dual(1<<j)
        cols[j]=dual(1<<i)
        generators.append(tuple(f.mul(apply_basis(cols,x),f.inverse(x)) for x in range(1,f.size)))
    ratios=[0]*(f.size-1)
    checks=direct=0
    shifts=Random(75)
    for t in range(1<<len(generators)):
        if t:
            row=generators[(t&-t).bit_length()-1]
            ratios=[a^b for a,b in zip(row,ratios)]
        good=((1<<f.size)-1)^sum(1<<s for s in set(ratios))
        for x,s in enumerate(ratios,1):
            if not s:
                assert (good&lines[x]).bit_count()%2
                checks+=1
        if t<64 or t%379==0:
            c=shifts.randrange(f.size)
            cols=[f.mul(ratios[(1<<i)-1]^c,1<<i) for i in range(d)]
            assert _center(f,cols)==c
            ans=find_columns(f,cols)
            assert (good>>(ans^c))&1
            a=list(linearized(f,cols))
            assert a[0]==c
            a[0]=0
            D=dickson(f,a)
            for line in {v for v in lines[1:]}:
                rep=(line&-line).bit_length()-1
                assert parity(f,D,rep)==(good&line).bit_count()%2
            direct+=1
    return checks,direct


if __name__=='__main__':
    print([audit(mod) for mod in (19,67)])
