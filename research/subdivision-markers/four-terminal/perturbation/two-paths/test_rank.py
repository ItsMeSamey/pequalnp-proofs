from random import Random
from root_rank import pruned_query
from contract import is_circuit

if __name__=='__main__':
    rng=Random(17223);counts=[0]*7;covered=passed=0
    for _ in range(3000):
        c=rng.randrange(1,5);start=0;edges=[];paths=[]
        for j in range(c):
            path=[]
            for k in range(rng.randrange(1,4)):
                path.append((len(edges),start,start+1));edges.append((start,start+1,rng.randrange(2)))
                start+=1
            paths.append(path);start+=1
        n=start+rng.randrange(2)
        edges.extend((rng.randrange(n),rng.randrange(n),rng.randrange(2)) for j in range(rng.randrange(7)))
        D=rng.randrange(1,1<<n);root={i for path in paths for i,_,_ in path}
        I={v for path in paths for _,_,v in path[:-1]}
        dim,cons,answer=pruned_query(n,edges,D,paths);counts[dim]+=1
        if cons and dim>3:continue
        free=[j for j,(a,b,g) in enumerate(edges) if j not in root and a not in I and b not in I]
        true=[]
        for mask in range(1<<len(free)):
            sub=root|{j for k,j in enumerate(free) if mask>>k&1}
            if is_circuit([(1<<edges[j][0])^(1<<edges[j][1])^(D*edges[j][2]) for j in sub]):
                true.append(sub)
        assert (answer is not None)==bool(true)
        assert answer is None or answer in true
        covered+=1;passed+=bool(true)
    print('rank-profile',counts,'covered',covered,'positive',passed)
    paths=[[(0,0,1),(1,1,2)],[(2,3,4)],[(3,5,6)]]
    ends=[(0,1),(1,2),(3,4),(5,6),(2,0),(3,4),(5,6),(0,0),(2,3),(4,5)]
    edges=[(a,b,int(i==7)) for i,(a,b) in enumerate(ends)]
    assert pruned_query(7,edges,3,paths)[:2]==(4,True)
    edge_cases=[0]*5
    for k in range(600):
        edges=[(a,b,rng.randrange(2)) for a,b in ends]
        D=rng.randrange(1,1<<7)
        dim,cons,answer=pruned_query(7,edges,D,paths)
        edge_cases[dim]+=1
        if not cons or dim<=3:
            root=set(range(4));true=[]
            for mask in range(1<<(len(edges)-4)):
                sub=root|{i for i in range(4,len(edges)) if mask>>(i-4)&1}
                if is_circuit([(1<<edges[j][0])^(1<<edges[j][1])^(D*edges[j][2]) for j in sub]):true.append(sub)
            assert (answer is not None)==bool(true)
            assert answer is None or answer in true
    print('three-path host rank profile',edge_cases,'and tight compatible rank-four example')
