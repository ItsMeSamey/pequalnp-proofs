"""Decode stream moments (M0=all prefix survivors, then ordinary positive orders)."""
from fractions import Fraction as F
from late_residual_primitive import linear,roots


def decode(m,moments,models=None):
    if m<0 or not moments or any(v<0 for v in moments): raise ValueError('invalid input')
    base=moments[0]
    if models is not None and not 0<=models<=base: raise ValueError('invalid model count')
    if not m or not base or models==base: return base,{}
    shift=models is None
    moments=list(moments[1:]) if shift else [base-models,*moments[1:]]
    if moments and moments[0]==0: return base,{}
    for s in range(1,(len(moments)-1)//2+1):
        q=linear([moments[i:i+s] for i in range(s)],[-moments[i+s] for i in range(s)])+[F(1)]
        if sum(q[i]*q[j]*moments[i+j] for i in range(s+1) for j in range(s+1)): continue
        vals=roots(q,m)
        if len(vals)!=s or any(sum(c*v**i for i,c in enumerate(q)) for v in vals): raise ValueError('invalid roots')
        ws=linear([[v**i for v in vals] for i in range(s)],moments[:s])
        if shift: ws=[w/v for w,v in zip(ws,vals)]
        if any(w.denominator!=1 or w<=0 for w in ws): raise ValueError('invalid multiplicity')
        return base-int(sum(ws)),dict(zip(vals,map(int,ws)))
    return None
