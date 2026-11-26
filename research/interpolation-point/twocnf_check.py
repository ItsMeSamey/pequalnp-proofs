from itertools import combinations
from random import Random

rng=Random(5704)
def rref(rows,p):
    piv={}
    for x in rows:
        x=list(x)
        for j,b in sorted(piv.items()):
            x=[(a-x[j]*c)%p for a,c in zip(x,b)]
        j=next((i for i,e in enumerate(x) if e),None)
        if j is None: continue
        b=[e*pow(x[j],-1,p)%p for e in x]
        for h,y in list(piv.items()):
            piv[h]=[(a-y[j]*c)%p for a,c in zip(y,b)]
        piv[j]=b
    return tuple(tuple(row) for _,row in sorted(piv.items()))
def count(n,exc,models,p):
    # Use exhaustive preprocessing to isolate the basis DP under test.
    if not models:return 0
    witness=models[0]
    free=[i for i in range(n) if any((a^witness)>>i&1 for a in models)]
    graph=set()
    conflicts=set()
    for idx,bits in exc:
        if len(idx)!=2 or any(i not in free for i in idx):continue
        i,j=idx
        pat=tuple(v^(witness>>k&1) for v,k in zip(bits,idx))
        if pat==(1,1):conflicts.add((i,j))
        elif pat==(1,0):graph.add((i,j))
        elif pat==(0,1):graph.add((j,i))
    reach=set(graph)|{(i,i) for i in free}
    for v in free:
        reach|={(i,j) for i in free for j in free if (i,v) in reach and (v,j) in reach}
    groups=[]
    todo=set(free)
    while todo:
        v=next(v for v in sorted(todo) if all((u,v) not in reach or (v,u) in reach for u in todo))
        group=sorted(u for u in todo if (v,u) in reach and (u,v) in reach)
        groups.append(group)
        todo.difference_update(group)
    states={():1}; future=sum(groups,[])
    for block in groups:
        ahead=future[len(block):]; new={}
        for basis,w in states.items():
            for bit in (0,1):
                offset=0 if bit else 1
                if any(row[2*i+offset] for row in basis for i in range(len(block))): continue
                if bit and any((i,j) in conflicts for i,j in combinations(block,2)): continue
                rows=[row[2*len(block):] for row in basis]
                if bit:
                    for i in block:
                        rows.append([e for j in ahead for e in (int(tuple(sorted((i,j))) in conflicts),int((i,j) in graph))])
                key=rref(rows,p)
                new[key]=new.get(key,0)+w
        states=new; future=ahead
    return sum(states.values())
for trial in range(600):
    n=rng.randrange(2,9)
    exc=[((i,j),(u,v)) for i,j in combinations(range(n),2) for u in (0,1) for v in (0,1) if rng.randrange(13)==0]
    if rng.randrange(3)==0:exc.append(((rng.randrange(n),),(rng.randrange(2),)))
    models=[m for m in range(1<<n) if all(tuple(m>>i&1 for i in idx)!=b for idx,b in exc)]
    for p in (3,5):
        assert count(n,exc,models,p)==len(models)
print('1200 signed-basis counts over F3 and F5 verified')
