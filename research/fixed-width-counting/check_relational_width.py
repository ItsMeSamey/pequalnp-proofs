from itertools import product, combinations
from math import prod

def projection(rows, keys):
    return {tuple(row[k] for k in keys) for row in rows}

def primes(rows, keys):
    if not keys:
        return []
    pivot,*rest=keys
    x = next(iter(rows))[pivot]
    parts = primes({r for r in rows if r[pivot]==x},rest)
    recovered = []
    for part in parts:
        other = [k for k in keys if k not in part]
        if len(projection(rows,keys))==len(projection(rows,part))*len(projection(rows,other)):
            recovered.append(part)
    return recovered+[[k for k in keys if all(k not in p for p in recovered)]]

def literal_true(r,i,x):
    return r[i]!=2 and r[i]==x[i]

def verify(rows,n):
    keys=list(range(n))
    parts=primes(rows,keys)
    assert prod(len(projection(rows,p)) for p in parts)==len(rows)
    for p in parts:
        assert all(len(projection(rows,b))*len(projection(rows,[k for k in p if k not in b]))
                   >len(projection(rows,p)) for s in range(1,len(p)) for b in combinations(p,s))
    for anchor in ([],[0],keys):
        groups={}
        for row in rows:
            groups.setdefault(tuple(row[i] for i in anchor),set()).add(row)
        layout=[]
        for block in groups.values():
            parts=primes(block,[k for k in keys if k not in anchor])
            head=list(anchor)
            local=[]
            for p in parts:
                if len(projection(block,p))==1:
                    head+=p
                else:
                    local.append(p)
            layout.append((block,head,local))
        for x in product(range(2),repeat=n):
            expected=all(any(literal_true(r,k,x) for k in keys) for r in rows)
            signed=1
            for block,head,local in layout:
                row=next(iter(block))
                terms=1
                if not any(literal_true(row,k,x) for k in head):
                    sats=[all(any(literal_true(r,k,x) for k in p) for r in block) for p in local]
                    terms+=sum((-1)**(1+sum(mask)) for mask in product(range(2),repeat=len(local))
                               if all(not v or q for v,q in zip(mask,sats)))
                signed*=terms
            assert signed==expected

total=0
for n,alphabet in [(2,range(3)),(3,range(2))]:
    universe=list(product(alphabet,repeat=n))
    for mask in range(1,1<<len(universe)):
        verify({row for i,row in enumerate(universe) if mask>>i&1},n)
        total+=1
print(f"{total} complete relation families and three anchor choices checked")
