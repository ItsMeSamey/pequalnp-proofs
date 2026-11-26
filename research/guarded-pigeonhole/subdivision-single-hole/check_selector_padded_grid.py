"""Extract actual Boolean polar coefficients in the active gated copy of an explicit NO."""
from itertools import combinations, product
signs=list(product(range(2),repeat=3))  # all eight clauses -> unsatisfiable
assert all(not all(any(x^s for x,s in zip(truth,clause)) for clause in signs) for truth in signs)

def gain_rank(rows):
    basis={}
    for x in rows:
        while x:
            k=x.bit_length()
            if k not in basis:
                basis[k]=x;break
            x^=basis[k]
    return len(basis)

def forms(k, private):
    # One truth bit per original variable, one w per clause and private gadget variables.
    # Private gates attached to all logical variables/w, entirely on this shore.
    base=3+k
    nodes=base*(3 if private else 1)
    nxt=nodes; rows=[]
    def add(clause):
        nonlocal nxt
        arity=len(clause);start=nxt;nxt+=arity-1
        for idx,(v,neg) in enumerate(clause):
            def row(x,v=v,neg=neg,idx=idx,start=start,arity=arity):
                witness=((x>>(start+idx))&1) if idx<arity-1 else (1^((x>>start)&((1<<(arity-1))-1)).bit_count()%2)
                return (1^neg^((x>>v)&1))&witness
            rows.append(row)
    for i,(sx,sy,sz) in enumerate(signs[:k]):
        add([(0,sx),(3+i,0)])
        add([(3+i,1),(1,sy),(2,sz)])
    if private:
        for j in range(base):
            for par in combinations(range(3),1):
                add([(v,int(i in par)) for i,v in enumerate((j,base+2*j,base+2*j+1))])
            add([(j,1),(base+2*j,1),(base+2*j+1,1)])
    for fn in rows:
        c=fn(0);lin=[fn(1<<j)^c for j in range(nxt)]
        # Complete polar scan below also retains directions with zero linear coefficient.
        yield sum((fn(1<<i|1<<j)^lin[i]^lin[j]^c)<<p for p,(i,j) in enumerate(combinations(range(nxt),2)))

for k,priv in [(1,False),(3,False),(8,False),(1,True)]:
    P=list(forms(k,priv))
    assert gain_rank(P)==len(P)
    print(k,'clauses, private',priv,':',len(P),'independent polar rows')
