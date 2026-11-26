"""Fixed-p arbitrary support row search. Cutoffs return UNKNOWN."""
from itertools import product
from collections import defaultdict
from partial_atom import feasible
P=4099
ZERO=(0,0)
V={-1:ZERO,0:(1,0),1:(0,1),2:(P-1,0),3:(0,P-1)}
def mul(x,y):
    a,b=x;c,d=y
    return ((a*c-b*d)%P,(a*d+b*c)%P)
def sub(x,y):
    return ((x[0]-y[0])%P,(x[1]-y[1])%P)
def insert(basis,row):
    for j,pivot in sorted(basis.items()):
        a=row[j]
        if a!=ZERO:row=[sub(v,mul(a,b)) for v,b in zip(row,pivot)]
    j=next((k for k,a in enumerate(row[:-1]) if a!=ZERO),None)
    if j is None:return basis if row[-1]==ZERO else None
    a,b=row[j];den=pow((a*a+b*b)%P,-1,P)
    inv=(a*den%P,-b*den%P)
    return basis | {j:tuple(mul(v,inv) for v in row)}
def coefficients(basis,r):
    if len(basis)<r:return None
    sol=[ZERO]*r
    for j,row in sorted(basis.items(),reverse=True):
        rhs=row[-1]
        for a,c in zip(row[:-1],sol):rhs=sub(rhs,mul(a,c))
        sol[j]=rhs
    return sol

def fixed_patterns(domains,sol,rhs):
    half=len(sol)//2
    def sums(part,weights):
        for pat in product(*part):
            total=ZERO
            for v,c in zip(pat,weights):
                a,b=mul(V[v],c)
                total=((total[0]+a)%P,(total[1]+b)%P)
            yield total,pat
    buckets=defaultdict(list)
    for value,pat in sums(domains[:half],sol[:half]):buckets[value].append(pat)
    for value,right in sums(domains[half:],sol[half:]):
        for left in buckets.get(sub(rhs,value),[]):yield left+right

def patterns(n,cols,x,sol,rhs):
    domains=[];prev=[];last={}
    for j,col in enumerate(cols):
        sig=tuple(col.values());prev.append(last.get(sig));last[sig]=j
        allowed=[]
        for v in (range(-1,4) if any(y>=0 for y in sig) else [-1,0]):
            col[x]=v
            if feasible(n,col):allowed.append(v)
        del col[x];domains.append(allowed)
    for p in (product(*domains) if sol is None else fixed_patterns(domains,sol,rhs)):
        if all(k is None or p[k]<=p[j] for j,k in enumerate(prev)):yield p
def search(n,target,r,max_nodes=None):
    assert len(target)==1<<n and 1<=r<=7 and set(target)<={-1,1}
    cols=[{} for _ in range(r)];nodes=0
    def visit(x,basis):
        nonlocal nodes
        if max_nodes is not None and nodes>=max_nodes:raise TimeoutError
        nodes+=1
        if x==len(target):return [dict(c) for c in cols]
        rhs=(target[x]%P,0)
        sol=coefficients(basis,r)
        for pat in patterns(n,cols,x,sol,rhs):
            new=insert(basis,[V[v] for v in pat]+[rhs]) if sol is None else basis
            if new is None:continue
            for c,v in zip(cols,pat):c[x]=v
            witness=visit(x+1,new)
            for c in cols:del c[x]
            if witness is not None:return witness
        return None
    try:witness=visit(0,{})
    except TimeoutError:return 'UNKNOWN',None,nodes
    return ('SAT' if witness is not None else 'UNSAT'),witness,nodes
if __name__=='__main__':
    g=[1]*7+[-1]
    assert search(3,g,1)[0]=='UNSAT'
    assert search(3,g,2,5000)[0]=='SAT'
    assert search(3,g,2,0)[0]=='UNKNOWN'
    assert search(2,[1,1,1,-1],1)[0]=='SAT'
    print('four controls passed')
