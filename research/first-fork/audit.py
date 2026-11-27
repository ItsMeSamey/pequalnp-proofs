"""Full truth-table check of first-fork colors on circuits with AND/OR/NOT gates."""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
from random import Random

stats=Counter()
digest=sha256()
def audit(n,gates,taps):
    m=1<<n
    mask=(1<<m)-1
    vals=[sum(1<<x for x in range(m) if x>>i&1) for i in range(n)]
    active={}
    for i,(op,args) in enumerate(gates,n):
        reads=args[:1] if op=='N' else args
        active[i]=[a for a in reads if a<i]
        vs=[vals[a] if a<i else 0 for a in reads]
        if op=='N':
            val=mask^(vs[0] if vs else 0)
        else:
            val=mask if op=='A' else 0
            for z in vs: val=val&z if op=='A' else val|z
        vals.append(val)
    final=0
    users={}
    def trace(i,to):
        if i>=len(vals):return
        if i in users:
            users[i].append(to);return
        users[i]=[to]
        for a in active.get(i,()):trace(a,i)
    for t in taps:
        trace(t,-1)
        if t<len(vals):final|=vals[t]
    colors={}
    for i in range(n):
        u=i
        while u in users and len(users[u])==1:u=users[u][0]
        colors[i]=u if u in users else -1
    edges=[]
    for a,b in combinations(range(n),2):
        i,j=1<<a,1<<b
        tables=set()
        for x in range(m):
            if x&(i|j):continue
            tables.add(sum(((final>>(x|d))&1)<<k for k,d in enumerate((0,i,j,i|j))))
        if 8 in tables and 14 in tables:
            edges.append((a,b))
            assert colors[a]!=colors[b],(n,gates,taps,a,b,colors)
        if any(tbl in tables for tbl in (1,7)):stats['negative sections']+=1
    stats['circuits']+=1
    stats['conflict circuits']+=bool(edges)
    stats['edges']+=len(edges)
    stats['multiple taps']+=len(taps)>1
    stats['duplicate taps']+=len(set(taps))<len(taps)
    stats['live NOT']+=any(i in users and op=='N' for i,(op,_) in enumerate(gates,n))
    digest.update(repr((n,gates,taps,final,edges,colors)).encode()+b'\n')

def main():
    # Exhaust all ordered lists of 0..2 operands, all opcodes, and 1..2 taps.
    for op in 'AON':
        for ar in range(3):
            for pins in product(range(4),repeat=ar):
                for t in (1,2):
                    for taps in product(range(5),repeat=t):
                        audit(3,[(op,pins)],taps)
    rng=Random(725)
    for _ in range(6000):
        n=rng.choice((3,4,5));g=[]
        for i in range(n,n+rng.randrange(3,13)):
            g.append((rng.choice('AAOON'),tuple(rng.randrange(i+2) for _ in range(rng.choice((1,2,2,2))))))
        audit(n,g,tuple(rng.randrange(n+len(g)+1) for _ in range(rng.randrange(1,5))))
    # Plant majority(x,y,z), whose every pair has both positive sections.
    # Also push NOTs into/out of the multiplexer branches via De Morgan and
    # add random surrounding gates/taps so detected edges are nonvacuous.
    seed=[('A',(0,1)),('O',(0,1)),('A',(4,2)),('O',(3,5))]
    demorgan=[('N',(0,2)),('N',(1,2)),('O',(3,4)),('N',(5,)),('A',(3,4)),('N',(7,)),('A',(8,2)),('O',(6,9))]
    for g0 in (seed,demorgan):
        for _ in range(600):
            g=list(g0);root=len(g)+2
            for i in range(3+len(g),3+len(g)+rng.randrange(5)):
                g.append((rng.choice('AON'),(root,rng.randrange(i+1))));root=i
            audit(3,g,tuple([root]+[rng.choice([len(g0)+2,root,3+len(g)]) for _ in range(rng.randrange(3))]))
    print(dict(stats),digest.hexdigest())

if __name__=='__main__':main()
