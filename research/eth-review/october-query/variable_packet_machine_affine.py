"""DFS contraction with supplied arbitrary packet lengths, labels and active shells."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import prod
from one_packet_layer import Ring,canonical_lift,interpolate,recover,unit_inverse
from tapered_jet_machine import valuation,inverse_odd
from packet_entry_tape import packet_entry


@dataclass(frozen=True)
class Description:
    ring: Ring
    rows: tuple       # (local coefficients, list of (target index,mode coefficient))
    columns: int
    beta: tuple
    sources: tuple    # (list of scalar weights of local columns,exponent)

    @property
    def birth(self): return self.ring.p

    def word(self,bits):
        r=self.ring
        y=bits[:len(self.rows)]
        x=bits[len(y):]
        forms=[]
        for sign,(local,terms) in zip(y,self.rows):
            b=r.scalar(0)
            for pick,w in zip(x,local):
                if pick:b=r.add(b,w)
            forms.append((b if sign else r.add(r.scalar(1),r.neg(b)),
                          terms if sign else [(j,r.neg(w)) for j,w in terms]))
        src=[(r.scalar(sum(c for c,b in zip(ws,x) if b)),ex) for ws,ex in self.sources]
        return packet_entry(r,forms,self.beta,src)


def shifted_kernel(r,L,t,zeta,delta):
    G=range(-L,L)
    denominator=prod(-q for q in G if q)
    poly=[1]
    for q in G:
        if q==delta:continue
        nxt=[0]*(len(poly)+1)
        for j,c in enumerate(poly):
            nxt[j]+=(t-q)*c
            nxt[j+1]+=2*L*c
        poly=nxt
    out=r.scalar(0)
    for c in reversed(poly):
        frac=Fraction(c,denominator)
        assert frac.denominator%2
        out=r.add(r.mul(out,zeta),r.scalar(frac.numerator*inverse_odd(frac.denominator,r.p)))
    return out


def solve(network,m,p,f,ell,level,plan,terminal=None):
    r=Ring(p,f,ell)
    for side in network:
        assert sorted(e for _,edges in side for e in edges)==list(range(m))
    spec=plan(network,m,level) if m else None
    if spec is None:
        if terminal is not None:
            projected=terminal(network,m,r)
            if projected is not None: return projected
        acc=r.scalar(0)
        for x in range(1<<m):
            v=r.scalar(1)
            for side in network:
                for desc,edges in side:
                    word=desc.word(tuple((x>>j)&1 for j in edges))
                    v=r.mul(v,canonical_lift(word,desc.birth,p))
            acc=r.add(acc,v)
        return acc
    # Each packet is an ordered length-L tuple of edge IDs/None. Labels are given
    # per shell i, shore and old vertex, never per port of a retained vertex.
    a,u,packets,labels=spec
    L=1<<a
    assert 1<=u<=min(m,a) and all(len(q)==L for q in packets)
    assert sorted(e for q in packets for e in q if e is not None)==list(range(m))
    degree=m*(2*L-1)
    assert degree+1<=1<<len(f)
    h=(3*m+u-1)//u
    jets={}
    for t in range(-L,L):
        if not t or valuation(t)>=u:continue
        i=valuation(t); step=1<<(i+1)
        pt=p+8*h*(L>>i)+8*m*(a+1)
        rr=Ring(pt,f,ell);mod=1<<pt
        groups=sorted(set(g for side in labels[i] for g in side))
        label=[{e:g for (_,edges),g in zip(network[j],labels[i][j],strict=True) for e in edges}
               for j in (0,1)]
        points=[tuple((j>>b)&1 for b in range(len(f)))+(0,)*(len(f)*(ell-1)) for j in range(degree+1)]
        values=[]
        for zeta in points:
            kern={d:shifted_kernel(rr,L,t,zeta,d) for d in range(1-L,L)}
            modes=[]; coeff={}; moments={}
            for qid,q in enumerate(packets):
                row_sites=[x for x,e in enumerate(q) if e is not None]
                for y0 in range(step):
                    cols=[y for y in row_sites if y%step==y0]
                    if not cols:continue
                    source=label[1][q[cols[0]]]
                    assert all(label[1][q[y]]==source for y in cols)
                    for target in groups:
                        if target==source:continue
                        xs=[x for x in row_sites if label[0][q[x]]==target]
                        if not xs:continue
                        assert all(valuation(t-y0+x)<=i and t-y0+x!=0 for x in xs)
                        for b in range(pt-1):
                            ws={y:pow((y-y0)//step,b,mod) for y in cols}
                            if not any(ws.values()):continue
                            key=(qid,source,target,y0,b)
                            any_nonzero=False
                            for x in xs:
                                c=t-y0+x
                                vi=valuation(c)
                                unit=rr.add(rr.scalar(c>>vi),rr.mul(rr.scalar((2*L)>>vi),zeta))
                                ratio=rr.mul(rr.scalar(step>>vi),unit_inverse(rr,unit))
                                w=rr.mul(kern[y0-x],rr.power(ratio,b))
                                if w!=rr.scalar(0):coeff[key,x]=w;any_nonzero=True
                            if any_nonzero:
                                modes.append(key);moments[key]=ws
            total=rr.scalar(0);beta={}
            def tuples(j,left):
                nonlocal total
                if j!=len(modes):
                    z=modes[j];qid,_,target,_,b=z
                    cap=sum(e is not None and label[0][e]==target for e in packets[qid])
                    for v in range(min(cap,left//(b+1))+1):
                        beta[z]=v;tuples(j+1,left-v*(b+1))
                    return
                val=rr.scalar(1)
                for g in groups:
                    names={};old=[];new=[]
                    for side in (0,1):
                        for (desc,edges),owner in zip(network[side],labels[i][side]):
                            if owner!=g:continue
                            ids=[]
                            for e in edges:
                                names[side,e]=len(names);ids.append(names[side,e])
                            old.append((desc,tuple(ids)))
                    for qid,q in enumerate(packets):
                        sites=[[x for x,e in enumerate(q) if e is not None and label[side][e]==g] for side in (0,1)]
                        rows,cols=sites
                        if not rows and not cols:continue
                        tar=[z for z in modes if z[0]==qid and z[2]==g and beta[z]]
                        src=[z for z in modes if z[0]==qid and z[1]==g and beta[z]]
                        affine=tuple((tuple(kern[y-x] for y in cols),
                                      tuple((j,coeff[z,x]) for j,z in enumerate(tar) if (z,x) in coeff))
                                     for x in rows)
                        desc=Description(rr,affine,len(cols),tuple(beta[z] for z in tar),
                                  tuple((tuple(moments[z].get(y,0) for y in cols),beta[z]) for z in src))
                        new.append((desc,tuple(names[side,q[x]] for side in (0,1) for x in sites[side])))
                    val=rr.mul(val,solve((old,new),len(names),pt,f,ell,level+1,plan,terminal))
                total=rr.add(total,val)
            tuples(0,pt-1)
            values.append(total)
        jets[t]=interpolate(rr,points,values)[:h*(u-i)]
    return tuple(recover(a,u,m,p,len(f)*ell,lambda t,j,c,prec:jets[t][j][c]))
