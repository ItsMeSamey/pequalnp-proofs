"""Independent Vandermonde and dual-coordinate checks for exposed pin factors."""
from itertools import combinations
from punctured_witness import BinaryField
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import subfield_basis
from hidden_product_network import encoder
from affine_binomial import power
from additive_slope_prefix import _det


def trace(f,x,a):
    s=0
    for _ in range(a):
        s^=x
        x=f.mul(x,x)
    assert s in (0,1)
    return s


if __name__=='__main__':
    count=0
    for mod in (7,19,67,283,1033,4105):
        f=BinaryField(mod)
        a=f.m//2
        basis=subfield_basis(f)
        H=[apply_basis(basis,j) for j in range(1<<a)]
        theta=next(v for v in H if len({power(f,v,1<<i) for i in range(a)})==a)
        alpha=[power(f,theta,j) for j in range(a)]
        columns=[sum(trace(f,f.mul(x,z),a)<<i for i,z in enumerate(alpha)) for x in basis]
        inv=encoder(columns)
        dual=[apply_basis(basis,inv(1<<j)) for j in range(a)]
        for t in H:
            word=sum(trace(f,f.mul(t,z),a)<<j for j,z in enumerate(alpha))
            assert apply_basis(dual,word)==t
        for k in range(a+1):
            for up in combinations(range(a),k):
                D=[[power(f,alpha[j],1<<i) for j in range(k)] for i in up]
                expected=1
                for i,j in combinations(up,2):
                    expected=f.mul(expected,power(f,theta,1<<i)^power(f,theta,1<<j))
                assert expected and _det(f,D)==expected
                count+=1
    print(count,'Vandermonde minors and all half-field dual-coordinate replays passed')

    from labeled_paired_line import Line,find_columns
    from random import Random
    rng=Random(315)
    parity_checks=answers=0
    for mod in (19,67,283,1033):
        f=BinaryField(mod)
        d=f.m
        # Prescribe one binary vector in the centered kernel by restricting
        # the alternating form to its complement; dense arbitrary scalar shift.
        encode_gram=encoder([f.trace_row(1<<j) for j in range(d)])
        for _ in range(2):
            a=rng.randrange(f.size)
            cols=[f.mul(a,1<<j) for j in range(d)]
            for i,j in combinations(range(1,d),2):
                if rng.randrange(2):
                    cols[i]^=encode_gram(1<<j)
                    cols[j]^=encode_gram(1<<i)
            bad={f.mul(apply_basis(cols,x),f.inverse(x)) for x in range(1,f.size)}
            line=Line(f,cols)
            safe=[word for word in range(1<<line.a)
                  if line.center^f.mul(line.scale,apply_basis(line.basis,word)) not in bad]
            for h in range(min(3,line.a-1)+1):
                for p in range(1<<h):
                    assert line.parity(p,h,stream=True)==line.parity(p,h)==sum((z&((1<<h)-1))==p for z in safe)%2
                    parity_checks+=1
            assert find_columns(f,cols,min(3,line.a-1),stream=True) not in bad
            assert find_columns(f,cols,min(3,line.a-1)) not in bad
            answers+=1
    print(parity_checks,'production prefix parities and',answers,'original slope witnesses')
