"""Ordinary binary circuit reduction by the rank of its root-coordinate restrictions."""
from contract import basis,exhaustive_oracle,reduce_vec

def reduce_roots(cols,roots,oracle=exhaustive_oracle):
    if not roots:raise ValueError('nonempty roots required')
    independent={}
    kernel=[]
    for i,col in enumerate(cols):
        x,used=reduce_vec(col,independent)
        support=used^(1<<i)
        if x:independent[x.bit_length()-1]=x,support
        else:kernel.append(support)
    eq={};reps=[];consistent=True
    for j in roots:
        form=sum((supp>>j&1)<<k for k,supp in enumerate(kernel))
        a,rhs=reduce_vec(form,eq)
        if a:
            eq[a.bit_length()-1]=a,1^rhs
            reps.append(j)
        elif rhs!=1:
            consistent=False
    if not consistent:return len(reps),False,None
    if len(reps)>3:return len(reps),True,None
    witness=oracle(cols,reps)
    assert witness is None or set(roots)<=set(witness)
    return len(reps),True,witness

def pruned_query(n,edges,D,paths):
    roots={i for path in paths for i,_,_ in path}
    strict={b for path in paths for _,_,b in path[:-1]}
    ids=[i for i,(a,b,g) in enumerate(edges) if i in roots or (a not in strict and b not in strict)]
    cols=[(1<<a)^(1<<b)^(D*g) for a,b,g in [edges[i] for i in ids]]
    dim,consistent,witness=reduce_roots(cols,[j for j,i in enumerate(ids) if i in roots])
    assert dim<=len(paths)+1
    return dim,consistent,None if witness is None else {ids[j] for j in witness}
