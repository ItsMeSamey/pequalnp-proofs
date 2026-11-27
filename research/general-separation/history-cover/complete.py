"""Exact original circuit decision using affine projection and guarded backends."""
from cover import direct,System
from triangular_backend import backend
from character_backend import Unsupported
from quadratic_parse import affine_domain
from sparse_decision import Limit,solve as sparse

def rebase(n,gates,out):
    eq=[(out>>1,1^(out&1))]
    while True:
        flat=affine_domain(n+len(gates),eq)
        if flat is None:
            return None
        o,dirs,_=flat
        def chart(f):
            return ((f&1)^((f>>1 & o).bit_count()&1)) | sum(
                ((f>>1 & v).bit_count()&1)<<(i+1) for i,v in enumerate(dirs))
        new=[]
        for i,(a,b,w) in enumerate(gates):
            c=w^(2<<(n+i))
            u,v,h=chart(a),chart(b),chart(c)
            if h==1:
                new.extend(f for f in (a^1,b^1) if chart(f))
            if u<=1:
                f=c^(b if u else 0)
            elif v<=1:
                f=c^(a if v else 0)
            elif u==v:
                f=c^a
            elif u^v==1:
                f=c
            else:
                continue
            if chart(f):
                new.append(f)
        if not new:
            break
        eq.extend((f>>1,f&1) for f in new)
    mask=(1<<n)-1
    base=o&mask
    piv={}
    for d in dirs:
        v=d&mask
        while v:
            p=v.bit_length()-1
            if p not in piv:
                piv[p]=v
                break
            v^=piv[p]
    basis=list(piv.values())
    def convert(f):
        raw=(f>>1)&mask
        return ((f&1)^((raw&base).bit_count()&1)) | sum(
            ((raw&d).bit_count()&1)<<(j+1) for j,d in enumerate(basis)) | (
            (f>>(n+1))<<(len(basis)+1))
    return base,basis,[tuple(map(convert,g)) for g in gates],convert(out)

def solve(n,gates,out,*,terms=64,work=5000,rank=4):
    if n<0 or min(terms,work,rank)<0 or out<0 or out>>(n+len(gates)+1):
        raise ValueError('invalid input')
    for i,g in enumerate(gates):
        if len(g)!=3 or any(v<0 or v>>(n+i+1) for v in g):
            raise ValueError('invalid gate')
    reduced=rebase(n,gates,out)
    if reduced is None:
        return None,'affine contradiction'
    base,basis,g,f=reduced
    d=len(basis)
    try:
        witness,_=sparse(d,g,f,terms,work)
        route='sparse'
    except Limit:
        sys=System(d,[(2<<(d+i),[(a,b),(c,)]) for i,(a,b,c) in enumerate(g)],[(f,)])
        try:
            _,witness=sys.count_witness(backend(sys,rank))
            route='triangular Gaussian'
        except Unsupported:
            witness=next((x for x in range(1<<d) if direct(d,g,f,x)),None)
            route='exhaustive'
    if witness is None:
        return None,route
    lift=base
    for i,v in enumerate(basis):
        if witness>>i&1:
            lift^=v
    assert direct(n,gates,out,lift)
    return lift,route

def from_cnf(n,clauses):
    gates=[]
    acc=1
    for clause in clauses:
        if len(clause)>3 or any(x==0 or abs(x)>n for x in clause):
            raise ValueError('invalid clause')
        bad=1
        for literal in clause:
            false_lit=(1<<abs(literal))^int(literal>0)
            gates.append((bad,false_lit,0))
            bad=2<<(n+len(gates)-1)
        gates.append((acc,bad^1,0))
        acc=2<<(n+len(gates)-1)
    return gates,acc
