"""Reduced-label Pfaffian contraction on a kernel-selected half-field line."""
from itertools import combinations
from additive_safe_slope import _safe
from additive_slope_prefix import dickson
from hidden_product_network import encoder
from kernel_half_line import selected_line
from label_subset_ring import LabelRing
from product_slack import linearized
from paired_line_stream_ring import StreamRing,DualRing
from punctured_chart_witness import power_chart
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import subfield_basis
from sparse_line_prefix import dual_basis


class Ring(LabelRing):
    def scalar(self,c):
        return (c,)+(0,)*(self.size-1)

    def scale(self,c,x):
        return tuple(self.field.mul(c,v) for v in x)

    def unit_inverse(self,x):
        inv=self.field.inverse(x[0])
        return self.scale(self.field.mul(inv,inv),x)

    def mul(self,x,y):
        if not any(x) or not any(y):
            return self.zero
        if not any(x[1:]):
            return self.scale(x[0],y)
        if not any(y[1:]):
            return self.scale(y[0],x)
        return super().mul(x,y)


def labels(r,linear,constants,values):
    """Evaluate merged digits after a zero-constant substitution of pin labels."""
    B=[r.zero]*len(linear[0])
    affine=r.one
    for powers,c,v in zip(linear,constants,values):
        if c:
            affine=r.mul(affine,r.add(r.one,v))
        for i,alpha in enumerate(powers):
            carry=r.scale(alpha,v)
            while any(carry):
                old=B[i]
                B[i]=r.add(old,carry)
                carry=r.mul(old,carry)
                i=(i+1)%len(B)
    return B,affine


def field_inverse_matrix(f,A):
    n=len(A)
    M=[row[:]+[int(i==j) for j in range(n)] for i,row in enumerate(A)]
    for i in range(n):
        j=next(j for j in range(i,n) if M[j][i])
        M[i],M[j]=M[j],M[i]
        inv=f.inverse(M[i][i])
        M[i]=[f.mul(inv,x) for x in M[i]]
        for j in range(n):
            if i!=j:
                c=M[j][i]
                M[j]=[u^f.mul(c,v) for u,v in zip(M[j],M[i])]
    return [row[n:] for row in M]


def det_unit(r,matrix):
    a=[row[:] for row in matrix]
    out=r.one
    for i in range(len(a)):
        j=next(j for j in range(i,len(a)) if a[j][i][0])
        a[i],a[j]=a[j],a[i]
        out=r.mul(out,a[i][i])
        inv=r.unit_inverse(a[i][i])
        for j in range(i+1,len(a)):
            factor=r.mul(inv,a[j][i])
            for k in range(i+1,len(a)):
                a[j][k]=r.add(a[j][k],r.mul(factor,a[i][k]))
    return out


def pfaffian(r,M):
    """Interpolate Pf(M+XJ) using only unit paired pivots."""
    if not M:
        return r.one
    f=r.field
    points=[]
    vals=[]
    for shift in range(f.size):
        a=[row[:] for row in M]
        for i in range(0,len(a),2):
            a[i][i+1]=r.add(a[i][i+1],r.scalar(shift))
        val=r.one
        for i in range(0,len(a),2):
            p=a[i][i+1]
            if not p[0]:
                break
            inv=r.unit_inverse(p)
            val=r.mul(val,p)
            for j in range(i+2,len(a)):
                for k in range(j+1,len(a)):
                    v=r.add(r.mul(a[i][j],a[i+1][k]),r.mul(a[i][k],a[i+1][j]))
                    a[j][k]=r.add(a[j][k],r.mul(v,inv))
        else:
            if not shift:
                return val
            points.append(shift)
            vals.append(val)
            if len(points)==len(a)//2+1:
                break
    if len(points)!=len(M)//2+1:
        raise ArithmeticError("insufficient regular interpolation points")
    out=r.zero
    for x,y in zip(points,vals):
        w=1
        for z in points:
            if z!=x:
                w=f.mul(w,f.mul(z,f.inverse(x^z)))
        out=r.add(out,r.scale(w,y))
    return out


def patterns(a,h):
    for i in range(min(h,a//2)+1):
        for switch in combinations(range(a),2*i):
            for start in (0,1):
                c=start
                digits=[]
                for j in range(a):
                    nxt=c^int(j in switch)
                    digits.append(1+2*nxt-c)
                    c=nxt
                yield digits


def reduced(f,linear,constants,up,active=None):
    h=len(linear)
    k=len(up)
    if active is None:
        r=Ring(f,h-k)
        free=[tuple(int(mask==1<<j) for mask in range(r.size)) for j in range(h-k)]
    else:
        r=StreamRing(f,h-k)
        t=(0,1)+r.zero[2:] if h>k else r.zero
        free=[t if active>>j&1 else r.zero for j in range(h-k)]
    values=[r.zero]*k+free
    if not k:
        B,c=labels(r,linear,constants,values)
        return r,B,c
    inv=field_inverse_matrix(f,[[linear[j][i] for j in range(k)] for i in up])
    for _ in range(h-k+1):
        B,_=labels(r,linear,constants,values)
        residual=[B[i] for i in up]
        if not any(any(z) for z in residual):
            break
        for j,row in enumerate(inv):
            for c,v in zip(row,residual):
                values[j]=r.add(values[j],r.scale(c,v))
    B,c=labels(r,linear,constants,values)
    if any(any(B[i]) for i in up):
        raise ArithmeticError("failed implicit label substitution")
    ext=DualRing(r)
    jac=[[] for _ in up]
    for j in range(k):
        lift=[v+r.zero for v in values]
        lift[j]=ext.add(lift[j],r.zero+r.one)
        deriv,_=labels(ext,linear,constants,lift)
        for row,i in zip(jac,up):
            row.append(deriv[i][r.size:])
    return r,B,r.mul(c,det_unit(r,jac))


class Line:
    def __init__(self,f,columns):
        self.f=f
        self.center,self.scale=selected_line(f,columns)
        if self.scale is None:
            return
        self.a=a=f.m//2
        sub=subfield_basis(f)
        encode=encoder(sub)
        def multiply(x,y):
            return encode(f.mul(apply_basis(sub,x),apply_basis(sub,y)))
        power=power_chart(a,1,multiply).basis if a>1 else (1,)
        self.normals=[apply_basis(sub,v) for v in power]
        self.basis=dual_basis(f,self.normals)
        self.weight=[self.scale]
        for _ in range(1,2*a):
            self.weight.append(f.mul(self.weight[-1],self.weight[-1]))
        coeff=list(linearized(f,columns))
        coeff[0]^=self.center
        self.D=[[f.mul(v,v) for v in row] for row in dickson(f,coeff)]

    def parity(self,prefix,h,*,stream=False):
        if not 0<=h<self.a or not 0<=prefix<1<<h:
            raise ValueError("prefix must leave a free digit")
        if not h:
            return 1
        f,a=self.f,self.a
        linear=[]
        for alpha in self.normals[:h]:
            powers=[]
            for _ in range(a):
                powers.append(alpha)
                alpha=f.mul(alpha,alpha)
            linear.append(powers)
        constants=[1^(prefix>>j&1) for j in range(h)]
        out=0
        for g in patterns(a,h):
            up=[i for i,v in enumerate(g) if v==3]
            subsets=range(1<<(h-len(up))) if stream else (None,)
            for active in subsets:
                r,B,weight=reduced(f,linear,constants,up,active)
                mandatory=[]
                optional=[]
                for i,kind in enumerate(g):
                    alpha,beta=self.weight[i],self.weight[i+a]
                    pair=f.mul(alpha,beta)
                    u={i:r.scalar(beta),i+a:r.scalar(alpha)}
                    if kind==0:
                        mandatory.extend(({i:r.one},{i+a:r.one}))
                    elif kind==1:
                        mandatory.append(u)
                        optional.append({i+a:r.scale(f.inverse(beta),B[i])})
                    elif kind==2:
                        weight=r.scale(pair,weight)
                        optional.append({j:r.scale(f.inverse(pair),r.mul(v,B[i])) for j,v in u.items()})
                    else:
                        weight=r.scale(pair,weight)
                if (len(mandatory)+len(optional))%2:
                    optional.append({})
                cols=mandatory+optional
                M=[[r.zero]*len(cols) for _ in cols]
                for i,j in combinations(range(len(cols)),2):
                    v=r.one if i>=len(mandatory) else r.zero
                    for k,x in cols[i].items():
                        for l,y in cols[j].items():
                            v=r.add(v,r.scale(self.D[k][l],r.mul(x,y)))
                    M[i][j]=v
                out^=r.mul(weight,pfaffian(r,M))[-1]
        if out not in (0,1):
            raise ArithmeticError("nonbinary pinned parity")
        return out


def find_columns(f,columns,depth=None,*,stream=False):
    line=Line(f,columns)
    if line.scale is None:
        return line.center
    a=line.a
    depth=7*a//50 if depth is None else depth
    if not 0<=depth<a:
        raise ValueError("invalid prefix depth")
    word=0
    for h in range(1,depth+1):
        if not line.parity(word,h,stream=stream):
            word|=1<<(h-1)
    for tail in range(1<<(a-depth)):
        s=line.center^f.mul(line.scale,apply_basis(line.basis,word|(tail<<depth)))
        if _safe(f,columns,s):
            return s
    raise ArithmeticError("no original safe shift in odd fiber")
