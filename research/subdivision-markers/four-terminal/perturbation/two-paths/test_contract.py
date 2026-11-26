from random import Random
from contract import is_circuit,reduce_paths

def check(n,edges,D,paths):
    roots={j for path in paths for j,_,_ in path}
    I={b for path in paths for _,_,b in path[:-1]}
    cols=[(1<<a)^(1<<b)^(D*g) for a,b,g in edges]
    full=[];pruned=[];two=[]
    free=sorted(set(range(len(edges)))-roots)
    for mask in range(1<<len(free)):
        C=roots|{j for k,j in enumerate(free) if mask>>k&1}
        if sum(edges[j][2] for j in C)%2 or not is_circuit([cols[j] for j in C]):continue
        full.append(C)
        if all(edges[j][0] not in I and edges[j][1] not in I for j in C-roots):pruned.append(C)
        used={v for j in C for v in edges[j][:2]}
        comp=[{v} for v in used]
        for j in C:
            a,b,_=edges[j]
            x=next(s for s in comp if a in s);y=next(s for s in comp if b in s)
            if x!=y:x.update(y);comp.remove(y)
        if len(C)-len(used)+len(comp)==2:two.append(C)
    ans=reduce_paths(n,edges,D,paths)
    assert (ans is not None)==bool(pruned)
    assert ans is None or ans in pruned
    assert bool(full)==bool(ans or two)
    return len(full),len(pruned),len(two)

if __name__=='__main__':
    rng=Random(19872);tested=0;tot=[0,0,0]
    for k in range(1500):
        lengths=[rng.randint(1,3) for _ in range(1+k%2)]
        n=sum(lengths)+len(lengths)+rng.randrange(3);paths=[];edges=[];start=0
        for l in lengths:
            path=[]
            for v in range(start,start+l):
                path.append((len(edges),v,v+1));edges.append((v,v+1,rng.randrange(2)))
            paths.append(path);start+=l+1
        edges.extend((rng.randrange(n),rng.randrange(n),rng.randrange(2)) for _ in range(rng.randint(2,7)))
        x=check(n,edges,rng.randint(1,(1<<n)-1),paths)
        tot=[a+b for a,b in zip(tot,x)];tested+=1
    for n,pairs,paths in [(5,[(0,1),(1,2),(3,4),(0,4),(2,3),(1,3),(0,3)], [[(0,0,1),(1,1,2)],[(2,3,4)]]),
                           (4,[(0,1),(1,2),(2,3),(0,3),(0,2),(1,3)], [[(0,0,1),(1,1,2),(2,2,3)]])]:
        for g in range(1<<len(pairs)):
            E=[(a,b,g>>i&1) for i,(a,b) in enumerate(pairs)]
            for D in range(1,1<<n):
                x=check(n,E,D,paths)
                tot=[a+b for a,b in zip(tot,x)];tested+=1
    print(tested,'cases; full, pruned, two-cycle support totals',tot)
