"""Small physical cycle controls and separate strict triangular-prism source tests."""
from itertools import combinations,product
from read_two_ring_nonzero import compile_nonzero
from two_boundary_kernel import project as kernel
from ring_image_two_boundary_phases import project,decide


def guard(u,v,a,b,c):
    return [(-a,b,-u),(-b,c,-u),(a,c,-u),(a,-b,-v),(b,-c,-v),(-a,-c,-v)]


def ok(rows,ones):
    return all(any((abs(l) in ones)==(l>0) for l in row) for row in rows)


def cactus(n,rows,dedicated):
    base=[]
    marks={}
    exterior=[]
    origins=[]
    used=0
    for i in range(1,n+1):
        occurrences=[(j,h,l) for j,row in enumerate(rows) for h,l in enumerate(row) if abs(l)==i]
        length=4*max(1,len(occurrences)) if dedicated else 4
        g=list(range(used+1,used+1+length))
        origins.append(g)
        for p,(j,h,l) in enumerate(occurrences):
            marks[j,h]=g[(4*p if dedicated else 0)+(l<0)]
        used+=length
    # Vertex j on a cycle touches edges j-1 and j. Join previous vertex 1 to next 0.
    for i in range(n-1):
        exterior.append(used+1+i)
    for i,g in enumerate(origins):
        for j,a in enumerate(g):
            star=[g[j-1],a]
            if j==0 and i:
                star.append(exterior[i-1])
            if j==1 and i+1<n:
                star.append(exterior[i])
            base.append(tuple(star))
            base.extend((-a,-b) for a,b in combinations(star,2))
    base.extend(tuple(marks[j,h] for h in range(len(row))) for j,row in enumerate(rows))
    return used+len(exterior),base,origins


def physical(n,rows,dedicated):
    arity,edge_rows,cycles=cactus(n,rows,dedicated)
    original=[set(i+1 for i,b in enumerate(bits) if b) for bits in product(range(2),repeat=n)]
    expected=[s for s in original if ok(rows,s)]
    raw=compile_nonzero(arity,edge_rows)
    args=tuple(raw[k] for k in ('n','clauses','point','k'))
    result=project(*args)
    assert result['status']=='projected',result['status']
    p=result['projection']
    for s in original:
        edge_ones={a for i,g in enumerate(cycles,1) for j,a in enumerate(g) if (j%2==0)==(i in s)}
        assert ok(edge_rows,edge_ones)==ok(rows,s)
        if ok(edge_rows,edge_ones):
            names={abs(l) for row in p.source_residual for l in row}
            seed=edge_ones & names
            assert ok(p.source_residual,seed)
            w=p.lift_source(seed)
            assert len(w)==arity and ok(edge_rows,{i+1 for i,b in enumerate(w) if b})
    ans=decide(*args)
    if ans['status']!='unknown':
        assert ans['status']==('nonzero' if expected else 'zero')
        if expected:
            assert ok(edge_rows,{i+1 for i,b in enumerate(ans['assignment']) if b})
    else:
        assert max(map(len,p.residual),default=0)>2
    return bool(expected)


def prism(unsat):
    edges=[(1,2),(2,3),(3,1),(4,5),(5,6),(6,4),(1,4),(2,5),(3,6)]
    private=[]
    assignments={}
    for j,(u,v) in enumerate(edges):
        a=7+3*j
        local=guard(u,v,a,a+1,a+2)
        private+=local
        for x,y in product(range(2),repeat=2):
            end={w for w,b in zip((u,v),(x,y)) if b}
            choices=[{a+k for k,b in enumerate(bits) if b} for bits in product(range(2),repeat=3)]
            good=[w for w in choices if ok(local,end|w)]
            assert bool(good)==(not(x and y))
            if good:
                assignments[j,x,y]=good[0]
    markers=(34,35,36)
    core=(37,38,39)
    other=[markers]
    for w in range(1,7):
        v=next(b if a==w else a for a,b in edges if w in (a,b))
        u=next(b if a==v else a for a,b in edges if v in (a,b) and w not in (a,b))
        other.append((-u,-v,w))
    for j,y in enumerate(markers+core):
        u,v=edges[j]
        s,h=edges[j+1]
        other.extend(((-u,-v,y),(-s,-h,-y)))
    core_rows=[tuple(-v if bits>>i&1 else v for i,v in enumerate(core))
               for bits in range(8 if unsat else 7)]
    full=private+other+core_rows
    K=kernel(39,full)
    for bdy in product(range(2),repeat=6):
        end={i+1 for i,b in enumerate(bdy) if b}
        if any({u,v}<=end for u,v in edges):
            continue
        extras=set().union(*(assignments[j,int(u in end),int(v in end)] for j,(u,v) in enumerate(edges)))
        feasible=False
        for b in product(range(2),repeat=3):
            picked=end|extras|set(markers)|{v for v,x in zip(core,b) if x}
            assert ok(full,picked)==ok(core_rows,picked)
            if ok(full,picked):
                feasible=True
                names={abs(l) for row in K.residual for l in row}
                assert ok(full,set(K.lift(picked&names)))
        assert feasible!=unsat
    variables=sorted({abs(l) for row in K.residual for l in row})
    if len(variables)<=12:
        assert any(ok(K.residual,{v for j,v in enumerate(variables) if w>>j&1})
                   for w in range(1<<len(variables)))!=unsat


def direct_boundary():
    rows=guard(1,2,3,4,5)
    for x,y in product(range(2),repeat=2):
        pinned=rows+[((1 if x else -1),),((2 if y else -2),)]
        K=kernel(5,pinned)
        feasible=False
        for bits in product(range(2),repeat=5):
            picked={i+1 for i,b in enumerate(bits) if b}
            if ok(K.residual,picked):
                feasible=True
                assert ok(pinned,set(K.lift(picked)))
        assert feasible==(not(x and y))


if __name__=='__main__':
    empty=kernel(1,[])
    assert set(empty.lift([1,1]))=={1}
    try:
        empty.lift([1,True])
    except ValueError:
        pass
    else:
        raise AssertionError("sparse lift accepted a bool alias after int 1")
    direct_boundary()
    prism(False)
    prism(True)
    assert physical(3,[(3,-1,2)],True)
    assert not physical(1,[(1,),(-1,)],True)
    assert physical(5,guard(2,1,5,3,4),False)
    print('Physical reduced cacti, four boundary rows and complete prism sources passed.')
