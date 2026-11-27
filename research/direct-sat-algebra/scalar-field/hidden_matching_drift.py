"""Recognize independent hidden field products plus arbitrary binary-affine drift.

Each polar block may have its own field degree. Coordinates use a left and
a right field input per block. Given a chart every target is attainable.
Schur pivot selection costs polynomial bit work in the input size and the
largest number of safe slopes at a visited pivot (possibly exponential in
the degree). Every returned witness is checked against the supplied ANF.
"""
from dataclasses import dataclass

from additive_safe_slope import find
from hidden_product_network import encoder
from product_slack import linearized
from punctured_chart import TableField
from punctured_chart_witness import power_chart
from quadratic_centroid import decompose, independent, zero_combinations
from quadratic_target import apply_basis, evaluate_anf, interpolate


@dataclass(frozen=True)
class Block:
    field: object
    left: tuple
    right: tuple
    output: tuple


def block_chart(domain,output,polar):
    degree = len(output)
    if degree == 0 or len(domain) != 2*degree:
        return None
    pair = next(((a,b) for i,a in enumerate(domain) for b in domain[i+1:] if polar(a,b)),None)
    if pair is None:
        return None
    p,r = pair
    unit = polar(p,r)
    axes = [zero_combinations(domain,lambda x:polar(x,v)) for v in (p,r)]
    if any(len(axis)!=degree for axis in axes):
        return None
    left,right = axes
    left_images = [polar(x,r) for x in left]
    right_images = [polar(p,x) for x in right]
    if any(len(independent(images))!=degree for images in (left_images,right_images)):
        return None
    basis = independent([unit,*output])
    if len(basis)!=degree:
        return None
    encode = encoder(basis)
    def align(axis,images):
        coordinates = encoder(images)
        return tuple(apply_basis(axis,coordinates(z)) for z in basis)
    left,right = align(left,left_images),align(right,right_images)
    table = TableField(tuple(tuple(encode(polar(x,y)) for y in right) for x in left))
    if not table.certify():
        return None
    field,powers = table,(1,)
    if degree>1:
        conversion = power_chart(degree,1,table.mul)
        field,powers = conversion.field,conversion.basis
    def convert(frame):
        return tuple(apply_basis(frame,z) for z in powers)
    return Block(field,convert(left),convert(right),convert(basis))


@dataclass(frozen=True)
class Chart:
    blocks: tuple
    constant: int
    drift: tuple
    input_basis: tuple
    output_basis: tuple

    def product(self,word):
        out = offset = 0
        for block in self.blocks:
            f = block.field
            a = word & (f.size-1)
            word >>= f.m
            b = word & (f.size-1)
            word >>= f.m
            out |= f.mul(a,b)<<offset
            offset += f.m
        return out

    def value(self,word):
        return self.constant ^ apply_basis(self.drift,word) ^ self.product(word)

    def witness(self,target,*,slope_finder=find):
        """Choose left inputs so the entire right-input linear map is invertible."""
        goal = encoder(self.output_basis)(target)
        columns = []
        left_word = 0
        offset = 0
        for block in self.blocks:
            f = block.field
            low = (1<<offset)-1
            inverse = encoder(tuple(c & low for c in columns))
            new = self.drift[2*offset+f.m:2*(offset+f.m)]
            schur = []
            for c in new:
                # Cancel earlier rows by a combination of earlier columns.
                correction = apply_basis(columns,inverse(c & low))
                schur.append(((c^correction)>>offset)&(f.size-1))
            slope = slope_finder(f,linearized(f,schur))
            if (type(slope) is not int or not 0<=slope<f.size or
                    len(independent(c^f.mul(slope,1<<i) for i,c in enumerate(schur)))!=f.m):
                raise ValueError("slope finder returned an unsafe pivot")
            left_word |= slope<<(2*offset)
            columns.extend(c ^ (f.mul(slope,1<<i)<<offset) for i,c in enumerate(new))
            offset += f.m
        right_word = encoder(columns)(goal ^ self.value(left_word))
        word = left_word
        offset = 0
        for block in self.blocks:
            f = block.field
            word |= ((right_word>>offset)&(f.size-1)) << (2*offset+f.m)
            offset += f.m
        if self.value(word)!=goal:
            raise ArithmeticError("Schur witness mismatch")
        return apply_basis(self.input_basis,word)


def recover(n,m,constant,linear,pairs):
    """Return a fully verified matching chart, or None for inconclusive recognition."""
    if n!=2*m:
        return None
    try:
        pieces = decompose(n,m,constant,linear,pairs,polar_only=True).blocks
    except ValueError:
        return None
    raw = lambda x:evaluate_anf(constant,linear,pairs,x)
    def polar(x,y):
        return constant^raw(x)^raw(y)^raw(x^y)
    blocks = []
    for domain,out in pieces:
        block = block_chart(domain,out,polar)
        if block is None:
            return None
        blocks.append(block)
    inputs = tuple(x for block in blocks for x in (*block.left,*block.right))
    outputs = tuple(y for block in blocks for y in block.output)
    encode = encoder(outputs)
    chart = Chart(tuple(blocks),encode(constant),tuple(encode(raw(x)^constant) for x in inputs),inputs,outputs)
    if interpolate(chart.value,n)!=interpolate(lambda word:encode(raw(apply_basis(inputs,word))),n):
        return None
    return chart


def solve(n,m,constant,linear,pairs,target,*,slope_finder=find):
    if not 0<=target<1<<m:
        raise ValueError("target outside output")
    chart = recover(n,m,constant,linear,pairs)
    if chart is None:
        return 'UNKNOWN',None
    x = chart.witness(target,slope_finder=slope_finder)
    if evaluate_anf(constant,linear,pairs,x)!=target:
        raise ArithmeticError("raw witness mismatch")
    return 'SAT',x


if __name__=='__main__':
    from additive_slope_prefix import find as prefix_find
    from random import Random
    from punctured_witness import BinaryField
    rng = Random(84107)
    def recoding(d):
        cols = [1<<j for j in range(d)]
        for _ in range(10*d):
            i,j = rng.sample(range(d),2)
            cols[i]^=cols[j]
        return cols
    for moduli in [(7,7),(7,11),(11,)]:
        fs = [BinaryField(p) for p in moduli]
        m=sum(f.m for f in fs)
        ib,ob = recoding(2*m),recoding(m)
        arbitrary = [rng.randrange(1<<m) for _ in ib]
        def raw(x):
            u=apply_basis(ib,x)^13
            y=7^apply_basis(arbitrary,u)
            k=0
            for f in fs:
                y ^= f.mul((u>>(2*k))&(f.size-1),(u>>(2*k+f.m))&(f.size-1))<<k
                k+=f.m
            return apply_basis(ob,y)
        anf=interpolate(raw,2*m)
        chart=recover(2*m,m,*anf)
        assert chart is not None
        for target in range(1<<m):
            assert raw(chart.witness(target))==target
        status,x=solve(2*m,m,*anf,1)
        assert status=='SAT' and raw(x)==1
        calls=[]
        def injected(field,coeffs):
            calls.append(field.m)
            return prefix_find(field,coeffs,prefix_bits=1)
        status,x=solve(2*m,m,*anf,1,slope_finder=injected)
        assert status=='SAT' and raw(x)==1
        assert sorted(calls)==sorted(f.m for f in fs)
    # Dimension-matched hostile polar with a radical and a zero output.
    assert solve(4,2,0,[0]*4,{(0,1):1},1)==('UNKNOWN',None)
    # A connected ring product over the dual numbers has nilpotents.
    ring=lambda x: ((x&1)*((x>>2)&1)) | ((((x&1)*((x>>3)&1))^(((x>>1)&1)*((x>>2)&1)))<<1)
    assert recover(4,2,*interpolate(ring,4)) is None
    assert solve(2,1,1,[1,1],{(0,1):1},0)[0]=='SAT'
    print('56 recoded targets, heterogeneous degrees, GF2, and two hostile controls passed')
