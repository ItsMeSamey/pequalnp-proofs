"""Verify a symmetric-varying field pencil in supplied raw binary frames.

fit(field, center_frames, leaf_frames, output_frames, constant, linear, pairs,
    input_offset=..., output_offset=..., diagonal_offsets=..., center_anchor=...)
returns a Chart or None. Chart.witness(raw_target) returns a checked raw input.
Each frame consists of m binary columns. All leaves and outputs are used.
There may be extra controls k>=r. Diagonal normalization is t_i=L_i(s)+b_i
with optional b_i; center_anchor selects the complementary affine section.
The full raw ANF, including every extra control, is verified before restriction.
"""
from dataclasses import dataclass
from itertools import combinations
from field_rank_drift import field_solve
from hidden_product_network import encoder
from quadratic_target import apply_basis,evaluate_anf,interpolate
from symmetric_overlap import witness as pencil_witness


def pack(f,values):
    return sum(a<<(f.m*j) for j,a in enumerate(values))


def chunks(f,x,n):
    return tuple((x>>(j*f.m))&(f.size-1) for j in range(n))


def dot(f,row,values):
    a=0
    for c,v in zip(row,values):
        a^=f.mul(c,v)
    return a


@dataclass
class Chart:
    field: object
    k: int
    r: int
    varying: tuple   # coefficient rows [output][leaf][original center]
    center_anf: tuple
    original_drift: tuple
    section_origin: int
    section_columns: tuple
    entries: dict
    section_drift: tuple
    raw_inputs: tuple
    input_offset: int
    raw_outputs: tuple
    output_offset: int
    raw_anf: tuple

    def witness(self,target):
        if not 0<=target<1<<len(self.raw_outputs):
            raise ValueError("raw target outside output space")
        f=self.field
        def center_word(t):
            return self.section_origin^apply_basis(self.section_columns,pack(f,t))
        def offset(t):
            return evaluate_anf(*self.center_anf,center_word(t))
        goal=encoder(self.raw_outputs)(target^self.output_offset)
        t,y=pencil_witness(f,self.r,self.entries,goal,offset,binary_drift=self.section_drift)
        z=center_word(t)|(y<<(self.k*f.m))
        raw=self.input_offset^apply_basis(self.raw_inputs,z)
        if evaluate_anf(*self.raw_anf,raw)!=target:
            raise ArithmeticError("invalid original ANF witness")
        return raw


def fit(field,center_frames,leaf_frames,output_frames,constant,linear,pairs,*,
        input_offset=0,output_offset=0,diagonal_offsets=None,center_anchor=0):
    f=field
    centers,leaves,outputs=(tuple(tuple(fr) for fr in frames)
                            for frames in (center_frames,leaf_frames,output_frames))
    k,r=len(centers),len(leaves)
    n=(k+r)*f.m
    o=len(outputs)*f.m
    linear=tuple(linear)
    if (any(len(fr)!=f.m for fr in (*centers,*leaves,*outputs)) or len(linear)!=n or
            any(not 0<=v<1<<n for fr in (*centers,*leaves) for v in fr) or
            any(not 0<=v<1<<o for fr in outputs for v in fr) or
            not 0<=input_offset<1<<n or not 0<=center_anchor<1<<(k*f.m) or
            any(not 0<=v<1<<o for v in (output_offset,constant,*linear,*pairs.values())) or
            any(not 0<=i<j<n for i,j in pairs)):
        raise ValueError("malformed raw frame, affine offset, or binary ANF")
    raw_inputs=tuple(v for fr in (*centers,*leaves) for v in fr)
    raw_outputs=tuple(v for fr in outputs for v in fr)
    encoder(raw_inputs)
    encode=encoder(raw_outputs)
    if len(outputs)!=r or k<r:
        return None
    b=(0,)*r if diagonal_offsets is None else tuple(diagonal_offsets)
    if len(b)!=r or any(not 0<=v<f.size for v in b):
        raise ValueError("invalid diagonal offsets")
    raw_anf=constant,linear,dict(pairs)
    def value(z):
        return encode(output_offset^evaluate_anf(*raw_anf,input_offset^apply_basis(raw_inputs,z)))
    cm=k*f.m
    width=r*f.m
    c,lin,cross=interpolate(value,n)
    g=(c,tuple(lin[:cm]),{(i,j):v for (i,j),v in cross.items() if j<cm})
    A=tuple(lin[cm:])
    if any(i>=cm for i,j in cross):
        return None
    varying=tuple(tuple(tuple((cross.get((a*f.m,cm+j*f.m),0)>>(i*f.m))&(f.size-1)
                              for a in range(k)) for j in range(r)) for i in range(r))
    if any(varying[i][j]!=varying[j][i] for i,j in combinations(range(r),2)):
        return None

    def homogeneous_column(s,j,scalar):
        return pack(f,[f.mul(dot(f,varying[i][j],s),scalar) for i in range(r)])
    # Compare every mixed coefficient, including all bit pairs of field inputs.
    for a in range(k):
        for h in range(f.m):
            s=[0]*k
            s[a]=1<<h
            for j in range(r):
                for u in range(f.m):
                    if cross.get((a*f.m+h,cm+j*f.m+u),0)!=homogeneous_column(s,j,1<<u):
                        return None
    diagonal=[varying[i][i] for i in range(r)]
    inverse=[]
    for j in range(r):
        col=field_solve(f,((row,int(i==j)) for i,row in enumerate(diagonal)),k)
        if col is None:
            return None
        inverse.append(col)
    section=tuple(pack(f,[f.mul(1<<h,v) for v in col]) for col in inverse for h in range(f.m))
    anchor=chunks(f,center_anchor,k)
    correction=pack(f,[dot(f,row,anchor)^v for row,v in zip(diagonal,b)])
    origin=center_anchor^apply_basis(section,correction)
    base=chunks(f,origin,k)
    entries={}
    for i,j in combinations(range(r),2):
        coeff=tuple(dot(f,varying[i][j],col) for col in inverse)
        if any(coeff):
            entries[i,j]=(0,coeff)
    drift=tuple(a^homogeneous_column(base,j,1<<h)
                for j in range(r) for h,a in enumerate(A[j*f.m:(j+1)*f.m]))
    return Chart(f,k,r,varying,g,A,origin,section,entries,drift,raw_inputs,input_offset,
                 raw_outputs,output_offset,raw_anf)


def check():
    from random import Random
    from punctured_witness import BinaryField
    from p3_binary_drift_sat import compile_cnf
    rng=Random(60143)
    def basis(n):
        B=[1<<i for i in range(n)]
        for _ in range(9*n):
            i,j=rng.sample(range(n),2)
            B[i]^=B[j]
        return tuple(B)
    count=0
    for mod,k,r in ((7,3,2),(11,3,3),(19,4,2)):
        f=BinaryField(mod); m=f.m; n=m*(k+r); o=m*r
        inp,out=basis(n),basis(o)
        xoff,yoff=rng.randrange(1<<n),rng.randrange(1<<o)
        decode=encoder(inp)
        # The third and later controls affect the homogeneous pencil even when
        # fixed by the witness section. Some controls also enter the diagonals.
        diag=[]
        for i in range(r):
            row=[int(j==i) for j in range(k)]
            if i+1<k:row[i+1]=2
            diag.append(row)
        V=[[None]*r for _ in range(r)]
        for i in range(r):
            V[i][i]=diag[i]
            for j in range(i):
                V[i][j]=V[j][i]=[rng.randrange(f.size) for _ in range(k)]
        if f.size==16:
            # Nonsymmetric K-linear constant operator: the native subfield line
            # branch is available even though symmetric Schur pivots do not apply.
            C=((3,5),(9,7))
            A=tuple(pack(f,[f.mul(C[i][j],1<<h) for i in range(r)])
                    for j in range(r) for h in range(m))
        else:
            A=tuple(rng.randrange(1<<o) for _ in range(o))
        def underlying(z):
            s=chunks(f,z,k); y=chunks(f,z>>(m*k),r)
            v=[0]*r
            for i in range(r):
                for j in range(r):
                    v[i]^=f.mul(dot(f,V[i][j],s),y[j])
            # Center-only ANF can be arbitrary binary quadratic, not K-linear.
            g=(z&1)*((z>>2)&1)*5 ^ (z&((1<<o)-1)) ^ 7
            return pack(f,v)^apply_basis(A,z>>(m*k))^g
        def raw(x):
            return yoff^apply_basis(out,underlying(decode(x^xoff)))
        frames=tuple(inp[s:s+m] for s in range(0,n,m))
        outputs=tuple(out[s:s+m] for s in range(0,o,m))
        data=interpolate(raw,n)
        offsets=tuple(rng.randrange(1,f.size) for i in range(r))
        opts=dict(input_offset=xoff,output_offset=yoff,diagonal_offsets=offsets,
                  center_anchor=rng.randrange(1<<(m*k)))
        chart=fit(f,frames[:k],frames[k:],outputs,*data,**opts)
        assert chart and chart.original_drift==A
        assert all(dot(f,row,chunks(f,chart.section_origin,k))==v for row,v in zip(diag,offsets))
        for t in range(min(64,1<<o)):
            w=chart.witness(t)
            assert raw(w)==t
            count+=1
        def reject(extra):
            corrupt=interpolate(lambda x:raw(x)^apply_basis(out,extra(decode(x^xoff))),n)
            assert fit(f,frames[:k],frames[k:],outputs,*corrupt,**opts) is None
        # Unsymmetric mixed dependence, an unexpected off-bit Walsh term, and
        # a pure leaf quadratic are distinct failure modes.
        reject(lambda z:f.mul(chunks(f,z,k)[-1],chunks(f,z>>(m*k),r)[1]))
        reject(lambda z:((z>>(m*(k-1)+1))&1)*((z>>(m*k+1))&1))
        reject(lambda z:((z>>(m*k))&1)*((z>>(m*k+1))&1))
        # Remove one diagonal on the entire center space, retaining symmetry.
        reject(lambda z:f.mul(dot(f,diag[0],chunks(f,z,k)),chunks(f,z>>(m*k),r)[0]))
        bad=list(frames[:k]); bad[0]=(0,*bad[0][1:])
        try:
            fit(f,bad,frames[k:],outputs,*data,**opts)
        except ValueError:
            pass
        else:
            raise AssertionError("accepted dependent input columns")

    # Use actual compiler rows/field-square drifts, and not just the dimension formula.
    f=BinaryField(7)
    sys=compile_cnf(f,1,[])
    k0=sys.vertices-len(sys.rows); r0=len(sys.rows)
    assert sys.vertices==6 and (k0,r0)==(2,4)
    def original(x):
        y=chunks(f,x,sys.vertices); vals=[]
        for j,(u,v,c,terms) in enumerate(sys.rows):
            v0=c^f.mul(y[u],y[v])
            for i,a in terms:v0^=f.mul(a,y[i])
            for i,a in sys.squares.get(j,()):v0^=f.mul(a,f.mul(y[i],y[i]))
            vals.append(v0)
        return pack(f,vals)
    n=sys.vertices*f.m
    unit=tuple((1<<(2*i),2<<(2*i)) for i in range(sys.vertices))
    assert fit(f,unit[:k0],unit[k0:],unit[:r0],*interpolate(original,n)) is None
    print(f"{count} dense raw targets verified; malformed, asymmetry, nonlinear, rank and actual compiled P3 controls passed")


if __name__=="__main__":
    check()
