"""Recognize triangular private controls from ordered leaf and output block bases.

The input is a packed vector quadratic, an ordered list of binary bases for
the leaf blocks, and an ordered list for the matching output blocks. The
control filtration, control coordinates, and all field structures are recovered.
"""
from dataclasses import dataclass

from additive_slope_prefix import find
from hidden_matching_drift import Block, block_chart
from hidden_product_network import encoder
from product_slack import linearized
from quadratic_centroid import independent, zero_combinations
from quadratic_target import apply_basis, evaluate_anf


def flatten(blocks):
    return tuple(x for block in blocks for x in block)


@dataclass
class Chart:
    blocks: tuple
    output_coordinates: object
    raw: object

    def witness(self,target,*,slope_finder=find):
        out=self.output_coordinates
        columns=[]
        control=offset=0
        for block in self.blocks:
            f=block.field
            low=(1<<offset)-1
            inv=encoder(tuple(c&low for c in columns))
            base=self.raw(control)
            new=[out(self.raw(control^y)^base) for y in block.right]
            effective=[((c^apply_basis(columns,inv(c&low)))>>offset)&(f.size-1) for c in new]
            slope=slope_finder(f,linearized(f,effective))
            if not 0<=slope<f.size:
                raise ValueError("invalid slope")
            control^=apply_basis(block.left,slope)
            base=self.raw(control)
            columns.extend(out(self.raw(control^y)^base) for y in block.right)
            offset+=f.m
        bits=encoder(columns)(out(target^self.raw(control)))
        x=control^apply_basis(flatten(b.right for b in self.blocks),bits)
        if self.raw(x)!=target:
            raise ArithmeticError("target replay failed")
        return x


def recover(n,m,constant,linear,pairs,leaves,outputs):
    leaves=tuple(map(tuple,leaves))
    outputs=tuple(map(tuple,outputs))
    leaf=flatten(leaves)
    if (n!=2*m or len(leaf)!=m or len(independent(leaf))!=m or
            list(map(len,leaves))!=list(map(len,outputs)) or any(not b for b in leaves) or
            len(independent(flatten(outputs)))!=m or
            any(not 0<x<1<<n for x in leaf) or any(not 0<y<1<<m for y in flatten(outputs))):
        return None
    raw=lambda x:evaluate_anf(constant,linear,pairs,x)
    def polar(x,y):
        return raw(x)^raw(y)^raw(x^y)^constant
    if any(polar(x,y) for j,x in enumerate(leaf) for y in leaf[:j]):
        return None
    controls=independent((*leaf,*(1<<i for i in range(n))))[m:]
    encode=encoder(flatten(outputs))
    offset=0
    blocks=[]
    for ys,os in zip(leaves,outputs):
        d=len(ys)
        low=(1<<offset)-1
        mask=(1<<d)-1
        def values(x):
            return tuple(encode(polar(x,y)) for y in ys)
        if any(v&low for x in controls for v in values(x)):
            return None
        kernel=tuple(zero_combinations(controls,lambda x:sum(v<<(m*i) for i,v in enumerate(values(x)))))
        cs=independent((*kernel,*controls))[len(kernel):]
        if len(cs)!=d:
            return None
        # A synthetic alternating map selects the two specified axes even
        # when the raw map has quadratic terms on the control space itself.
        frame=(*cs,*ys)
        split=encoder(frame)
        def mixed(x,y):
            a,b=split(x),split(y)
            u=polar(apply_basis(cs,a&mask),apply_basis(ys,b>>d))
            v=polar(apply_basis(cs,b&mask),apply_basis(ys,a>>d))
            return (encode(u^v)>>offset)&mask
        try:
            block=block_chart(frame,tuple(1<<j for j in range(d)),mixed)
        except ValueError:
            return None
        if block is None:
            return None
        # Verify every coefficient of the diagonal multiplication in its frames.
        for i,x in enumerate(block.left):
            for j,y in enumerate(block.right):
                expected=apply_basis(block.output,block.field.mul(1<<i,1<<j))
                if mixed(x,y)!=expected:
                    return None
        blocks.append(Block(block.field,block.left,block.right,
                            tuple(apply_basis(os,z) for z in block.output)))
        controls=kernel
        offset+=d
    if controls:
        return None
    return Chart(tuple(blocks),encoder(flatten(b.output for b in blocks)),raw)


if __name__=='__main__':
    from punctured_witness import BinaryField
    from quadratic_target import interpolate
    from random import Random
    rng=Random(3256)
    f=BinaryField(7)
    def dense(d):
        b=[1<<i for i in range(d)]
        for _ in range(10*d):
            i,j=rng.sample(range(d),2)
            b[i]^=b[j]
        return b
    inputs,outputs=dense(8),dense(4)
    unhide=encoder(inputs)
    def raw(x):
        z=unhide(x)^94
        a,b,u,v=[(z>>(2*i))&3 for i in range(4)]
        lo=f.mul(a,u)^f.mul(a,f.mul(v,v))^v^b
        hi=f.mul(b,v)^f.mul(a,b)^f.mul(f.mul(a,a),u)^u
        return apply_basis(outputs,lo|(hi<<2))^7
    leaves=[inputs[4:6],inputs[6:]]
    outs=[outputs[:2],outputs[2:]]
    anf=interpolate(raw,8)
    chart=recover(8,4,*anf,leaves,outs)
    assert chart
    for target in range(16):
        assert raw(chart.witness(target))==target
    def hostile(x):
        z=unhide(x)
        return raw(x)^apply_basis(outputs,f.mul(z>>4&3,z>>6&3))
    assert recover(8,4,*interpolate(hostile,8),leaves,outs) is None
    assert recover(8,4,*anf,leaves[::-1],outs) is None
    print('16 raw targets and two hostile triangular certificates passed')
