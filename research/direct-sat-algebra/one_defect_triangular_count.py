"""Exact directional-cut counts using a supplied or minimum-rank triangular completion."""
from quadratic_target import apply_basis,insert,parity
from one_defect_triangular_drift import minimum_completion


def count(rows,beta,*,certificate=None,state_cap=None):
    """Certificate is (U,V) with row i drift = sum_{j:U[i]_j=1} V[j]."""
    n=len(rows)
    if any(not 0<=v<1<<n for v in (*rows,beta)) or (state_cap is not None and state_cap<0):
        raise ValueError("invalid matrix, mark, or state cap")
    if certificate is None:
        V,U=minimum_completion(rows)
    else:
        U,V=map(tuple,certificate)
        if len(U)!=n or any(not 0<=v<1<<n for v in V) or any(not 0<=u<1<<len(V) for u in U):
            raise ValueError("invalid drift certificate")
        # Compress a supplied dependent signal basis, preserving the exact residual.
        echelon={}
        independent=[]
        coords=[]
        from quadratic_target import reduce_vector
        for v in V:
            if insert(v,1<<len(independent),echelon):
                independent.append(v)
            coords.append(reduce_vector(v,echelon)[1])
        V,U=independent,[apply_basis(coords,u) for u in U]
    D=[v^apply_basis(V,u) for v,u in zip(rows,U)]
    if any(v&((1<<i)-1) for i,v in enumerate(D)):
        raise ValueError("certificate residual must be upper triangular in the supplied order")
    r=len(V)
    columns=[sum(((v>>i)&1)<<j for j,v in enumerate(D) if j<i) for i in range(n)]
    widths=[]
    for cut in range(n+1):
        basis={}
        for col in columns[cut:]:
            insert(col&((1<<cut)-1),0,basis)
        widths.append(len(basis))
    meta=dict(rank=r,width=max(widths),peak=0)
    if not beta:
        return 0,None,meta
    obs=[sum(((v>>i)&1)<<j for j,v in enumerate(V))|(((beta>>i)&1)<<r) for i in range(n)]
    total=0
    witness=None
    def extend(table,key,ways,x):
        if key in table:
            old,rep=table[key]
            table[key]=old+ways,rep
        elif state_cap is not None and len(table)>=state_cap:
            return False
        else:
            table[key]=ways,x
        return True
    if state_cap==0:
        return None,None,meta
    for signal in range(1<<r):
        table={(0,0):(1,0)}
        meta['peak']=max(1,meta['peak'])
        for i in reversed(range(n)):
            nxt={}
            for (resp,syndrome),(ways,rep) in table.items():
                smaller=resp&((1<<i)-1)
                if not extend(nxt,(smaller,syndrome),ways,rep):
                    return None,None,meta
                if not (((resp>>i)&1)^((D[i]>>i)&1)^parity(U[i]&signal)):
                    if not extend(nxt,(smaller^columns[i],syndrome^obs[i]),ways,rep|(1<<i)):
                        return None,None,meta
                meta['peak']=max(meta['peak'],len(nxt))
            table=nxt
        ways,rep=table.get((0,signal|(1<<r)),(0,None))
        total+=ways
        if ways and witness is None:
            witness=rep
    return total,witness,meta
