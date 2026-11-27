"""Compile signed clauses to correlated physical OR and equality guards."""
from native_joint_guards import assemble,evaluate,solve

def clause_guard(labels,lits):
    k=len(lits);p=list(range(3*k))
    for j in range(k-1):
        a=3*j+1;b=3*(j+1)
        p[a],p[b]=p[b],p[a]
    r=0;s=3*(k-1)+1
    p=[s if v==r else r if v==s else v for v in p]
    return p,[(name,(1,0) if x>0 else (0,1))for name,x in zip(labels,lits)],r,s

def encode(clauses):
    ds={};guards=[]
    for ci,source in enumerate(clauses):
        source=tuple(source)
        if any(type(x) is not int or x==0 for x in source):raise ValueError('nonzero signed literals required')
        lits=list(dict.fromkeys(source))
        if any(-x in lits for x in lits):continue
        if not lits:return None,None
        labels=[(ci,j) for j in range(len(lits))]
        for label,x in zip(labels,lits):ds.setdefault(abs(x),[]).append(label)
        guards.append(clause_guard(labels,lits))
    for labels in ds.values():
        for a,b in zip(labels,labels[1:]):
            guards.append(((0,3,4,2,1,5),[(a,(0,1)),(b,(0,1))],1,2))
    return guards,ds

def solve_sat(clauses):
    clauses=[tuple(c) for c in clauses]
    guards,ds=encode(clauses)
    if guards is None:return None
    w=solve(guards)
    if w is None:return None
    vals={abs(x):0 for c in clauses for x in c}
    for v,labels in ds.items():
        vals[v]=w[labels[0]]
        assert all(w[i]==vals[v] for i in labels)
    assert all(any(bool(vals[abs(i)])==(i>0) for i in c) for c in clauses)
    return vals
