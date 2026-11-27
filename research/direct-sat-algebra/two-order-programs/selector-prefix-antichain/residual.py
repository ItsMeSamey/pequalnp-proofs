"""Absorb affine local constraints before checking the remaining equality-block shift space."""
from directed import TailOrbits,from_forbidden,insert,translate,ROOT,binary_model
import sys
sys.path.insert(0,str(ROOT/'mixed-ternary-native'))
from solver import chart,parity,lift

def certificate(front,A,B,basis):
    cols={v:sum(((w>>(v-1))&1)<<i for i,w in enumerate(basis)) for v in front}
    eq=[];blocked=[]
    for scope,source in A.items():
        if not scope:continue
        size=1<<len(scope)
        valid=[s for s in range(size) if not (translate(source,s)&~B[scope])]
        if not valid:return None
        if len(valid)==3:
            # Only the three-element subsets of a two-bit space are nonaffine.
            blocked.append((scope,next(s for s in range(size) if s not in valid)))
            continue
        for u in range(1,size):
            if all(not parity(u&(s^valid[0])) for s in valid):
                v=0
                for i,j in enumerate(scope):
                    if u>>i&1:v ^= cols[j]
                eq.append((v,parity(u&valid[0])))
    mapped=chart(len(basis),eq)
    if mapped is None:return None
    r,forms=mapped
    coordinate={}
    for scope,forbid in blocked:
        for v in scope:
            if v in coordinate:continue
            term=0
            for i,f in enumerate(forms):
                if cols[v]>>i&1:term ^= f
            coordinate[v]=term
    signatures=sorted({f>>1 for f in coordinate.values()}-{0})
    pivots={}
    for j,v in enumerate(signatures):insert(pivots,v,0)
    if len(pivots)!=len(signatures):return None  # uncertified comparison
    labels={s:i+1 for i,s in enumerate(signatures)}
    rows=[]
    for scope,forbid in blocked:
        row=[];possible=True
        for i,v in enumerate(scope):
            f=coordinate[v]
            b=((forbid>>i)&1)^(f&1)
            if f>>1:row.append(-labels[f>>1] if b else labels[f>>1])
            elif b:possible=False
        if possible:rows.append(tuple(row))
    y=binary_model(len(labels),rows)
    if y is None:return None
    K=chart(r,[(s,(y>>(i-1))&1) for s,i in labels.items()])
    if K is None:raise AssertionError('independent shift blocks failed lift')
    coeff=lift(forms,lift(K[1],0))
    word=0
    for i,w in enumerate(basis):
        if coeff>>i&1:word ^= w
    for scope,table in A.items():
        s=sum(((word>>(v-1))&1)<<j for j,v in enumerate(scope))
        if translate(table,s)&~B[scope]:raise AssertionError('invalid inclusion certificate')
    return word

class ResidualTranslation:
    directed=True
    def __init__(self,n):
        self.orbits=TailOrbits(n);self.strict=0;self.tests=0
    def __call__(self,j,front,D,E,banks,selectors):
        O=self.orbits
        left,_=O.key(j,front,D,banks,selectors)
        right,_=O.key(j,front,E,banks,selectors)
        if left==right:return True
        self.tests+=1
        shift=certificate(front,from_forbidden(front,D),from_forbidden(front,E),O.basis)
        if shift is not None:self.strict+=1
        return shift is not None
