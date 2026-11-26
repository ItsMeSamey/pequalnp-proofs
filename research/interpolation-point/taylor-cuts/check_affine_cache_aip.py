"""Explicit F_3 row certificates for affine local consistency of prism relations."""
from itertools import product


def prism(n, charges, pins=(), *, binary_marginals=False):
    """Return A,b, row names, ordered local states and a proposed row multiplier."""
    if n<3 or len(charges)!=2*n or len(pins)>n:
        raise ValueError("invalid prism dimensions")
    ends=[(k*n+i,k*n+(i+1)%n) for k in range(2) for i in range(n)]
    ends += [(i,n+i) for i in range(n)]
    scopes=[[(e,1 if u==v else -1) for e,(u,w) in enumerate(ends) if v==u or v==w]
            for v in range(2*n)]
    states=[]
    for v,scope in enumerate(scopes):
        domains=[range(3) if e<2*n else ((pins[e-2*n],) if e-2*n<len(pins) else (0,1))
                 for e,_ in scope]
        for values in product(*domains):
            if sum(a*sgn for a,(_,sgn) in zip(values,scope))%3==charges[v]%3:
                states.append((v,dict(zip((e for e,_ in scope),values))))
    rows=[]; rhs=[]; names=[]; coeff=[]
    for v in range(2*n):
        rows.append([int(w==v) for w,_ in states])
        rhs.append(1); names.append(("norm",v)); coeff.append(charges[v]%3)
    for e,(src,dst) in enumerate(ends):
        labels = (range(2) if e<2*n else range(1)) if binary_marginals else range(3 if e<2*n else 2)
        for label in labels:
            def cell(w,state):
                if w not in (src,dst):
                    return 0
                select=(state[e]>>label)&1 if binary_marginals else int(state[e]==label)
                return select*(1 if w==src else -1)
            rows.append([cell(w,s) for w,s in states])
            rhs.append(0); names.append(("edge",e,label))
            coeff.append(-(2**label if binary_marginals else label)%3)
    return rows,rhs,names,states,coeff


def certificate(rows,rhs,coeff):
    """Construct charge-weighted row multipliers normalized to c^T b=1, or None."""
    scale=sum(c*b for c,b in zip(coeff,rhs))%3
    if not scale:
        return None
    c=[x*pow(scale,-1,3)%3 for x in coeff]
    assert all(sum(x*y for x,y in zip(c,col))%3==0 for col in zip(*rows))
    assert sum(x*y for x,y in zip(c,rhs))%3==1
    return c


def run():
    cases=0
    for n in (3,4,5):
        placements=[(0,1),(n+1,2)]
        for index,charge in placements:
            charges=[0]*(2*n); charges[index]=charge
            for pins in [()]+list(product(range(2),repeat=n)):
                for binary in (False,True):
                    A,b,_,states,c=prism(n,charges,pins,binary_marginals=binary)
                    assert certificate(A,b,c) is not None
                    cases+=1
        # Feasible nonzero charges come from setting the first matching bit to one.
        flow=[0]*(2*n)+[1]+[0]*(n-1)
        charges=[0]*(2*n); charges[0]=1; charges[n]=-1
        for binary in (False,True):
            A,b,_,states,c=prism(n,charges,binary_marginals=binary)
            witness=[int(all(flow[e]==v for e,v in local.items())) for _,local in states]
            assert all(sum(a*x for a,x in zip(row,witness))==y for row,y in zip(A,b))
            assert certificate(A,b,c) is None
    A,b,names,_,c=prism(3,[1,0,0,0,0,0])
    print("replayed",cases,"refutations; 6 exact feasible integer witnesses")
    print("n=3 example nonzero named row multipliers:",
          [(name,x) for name,x in zip(names,certificate(A,b,c)) if x])

if __name__=='__main__':
    run()
