from random import Random
def cases():
 for seed in (309193,811723):
    g=Random(seed)
    def emit(tag,n,rows,oracle=None):
        ids=g.sample(range(1,n+1),n);raw=[]
        for row in rows:
            ls=[ids[abs(i)-1]*(1 if i>0 else -1) for i in row];g.shuffle(ls);raw.append(ls)
        g.shuffle(raw)
        return f'{seed}-{tag}',n,raw,oracle
    for k in (2,3,4):
        rows=[];t=k+1
        for i in range(k):
            s=i+1;x=k+2+5*i;y,u,v,z=x+1,x+2,x+3,x+4
            rows.extend([[s,-x],[s,-y],[-s,x],[s,-x,z]])
            for a,b in ((x,u),(y,v)):
                rows.extend([[t,-a,b],[t,a,-b],[-t,-a,-b],[-t,a,b]])
        for bad in (0,1):
            yield emit(f'narrow-{k}-{bad}',6*k+1,rows+([[t],[-t]] if bad else []),not bad)
    # Two dense tetrahedra glued along a face. All-min role heuristic
    # selects multiple variables in at least one scope of each tetrahedron.
    for flag in (0,1,2):
        import itertools
        rows=[]
        for cluster in ((1,2,3,4),(2,3,4,5)):
            for sc in itertools.combinations(cluster,3):
                rows.append([j*g.choice((-1,1)) for j in sc])
        if flag:rows += [[1],[-2],[3]]
        if flag==2:rows += [[-1,2,-3]]
        yield emit(f'tetra-{flag}',5,rows)
    # Directed implications guarded by separate raw pins; pair forces conflict.
    for bad in (0,1):
        rows=[[1,2,3],[-1,2,3],[1,-2,4],[-1,-2,4],[-3,-4,5],[-5,6],[-5,-6],[-2],[ -4 if bad else 4]]
        yield emit(f'guarded-conflict-{bad}',6,rows)
