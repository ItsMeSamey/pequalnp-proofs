"""Bounded m=8 replay with indexed support witnesses; no ambient wedge table."""
from collections import defaultdict, deque
from itertools import combinations
from frontier import basis


def grid_line(p,q):
    x,y=p; u,v=q
    if x!=u and y!=v:
        raise ValueError("axis-aligned segment required")
    dx=(u>x)-(u<x); dy=(v>y)-(v<y)
    return [(x+i*dx,y+i*dy) for i in range(max(abs(x-u),abs(y-v))+1)]


def path(points):
    result=[points[0]]
    for p,q in zip(points,points[1:]):
        result.extend(grid_line(p,q)[1:])
    return result


def replay():
    m=8
    width=4*m+2
    grid={(x,y):i for i,(x,y) in enumerate((x,y) for x in range(width+1) for y in range(-4,5))}
    apex=len(grid)
    sphere=[]
    for x in range(width):
        for y in range(-4,4):
            a,b,c,d=(grid[v] for v in ((x,y),(x+1,y),(x+1,y+1),(x,y+1)))
            sphere.extend(((a,b,c),(a,c,d)))
    rim=path([(0,-4),(width,-4),(width,4),(0,4),(0,-4)])
    sphere.extend((apex,grid[u],grid[v]) for u,v in zip(rim,rim[1:]))
    old_count=apex+1
    mids={}
    faces=[]
    for face in sphere:
        for a,b in combinations(face,2):
            e=tuple(sorted((a,b)))
            mids.setdefault(e,old_count+len(mids))
    offset=old_count+len(mids)
    for j,face in enumerate(sphere):
        for a,b in combinations(face,2):
            midpoint=mids[tuple(sorted((a,b)))]
            faces.extend(((a,midpoint,offset+j),(b,midpoint,offset+j)))
    incidence=defaultdict(list)
    for j,f in enumerate(faces):
        for a,b in combinations(f,2):
            incidence[tuple(sorted((a,b)))].append(j)
    V=offset+len(sphere)
    edges=list(incidence)
    assert V-len(edges)+len(faces)==2 and all(len(pair)==2 for pair in incidence.values())
    primal=[incidence[e] for e in edges]
    number={e:i for i,e in enumerate(edges)}

    def expand(p):
        vertices=[grid[w] for w in p]
        result=[vertices[0]]
        for a,b in zip(vertices,vertices[1:]):
            result.extend((mids[tuple(sorted((a,b)))],b))
        return result

    ts=[4*i+3 for i in range(m)]
    terminal={grid[(x,0)] for x in ts}
    tags=set()
    for a,b in zip(ts[::2],ts[1::2]):
        line=expand(grid_line((a,0),(b,0)))
        for z,w in zip(line,line[1:]):
            tags.symmetric_difference_update((number[tuple(sorted((z,w)))],))
    charge=set()
    for i in tags:
        charge.symmetric_difference_update(edges[i])
    assert charge==terminal

    def verify(first,second):
        first,second=set(first),set(second)
        adjacency=defaultdict(list)
        degree=[set(),set()]
        sizes=[0,0]
        for i,(z,w) in enumerate(edges):
            used=((z in first)!=(w in first),(z in second)!=(w in second))
            if any(used):
                a,b=primal[i]
                adjacency[a].append((b,int(i in tags)))
                adjacency[b].append((a,int(i in tags)))
                for j,on in enumerate(used):
                    if on:
                        sizes[j]+=1
                        degree[j].symmetric_difference_update((a,b))
        assert not any(degree)
        chart={}
        for seed in adjacency:
            if seed in chart:
                continue
            chart[seed]=0
            queue=deque([seed])
            while queue:
                u=queue.popleft()
                for v,t in adjacency[u]:
                    expected=chart[u]^t
                    if v not in chart:
                        chart[v]=expected;queue.append(v)
                    assert chart[v]==expected
        return sizes

    def arch(a,b,y):
        return expand(path([(a,0),(a,y),(b,y),(b,0)]))

    geometries=0
    for four in combinations(ts,4):
        for j in (1,2,3):
            p=(four[0],four[j]);q=sorted(set(four)-set(p))
            P=arch(*p,2);Q=arch(*q,-2)
            assert set(P).isdisjoint(Q)
            geometries+=1
    for a,b in combinations(ts,2):
        up=arch(a,b,2)
        outer=expand(path([(a,0),(a-1,0),(a-1,3),(b+1,3),(b+1,0),(b,0)]))
        assert set(up)&set(outer)=={grid[(a,0)],grid[(b,0)]}
        cycle=set(up)|set(outer)
        coords=[(0,-1)]
        for x in ts:
            if x not in (a,b):
                coords.extend([(x-1,-1),(x-1,0),(x,0),(x,-1)])
        coords.extend([(width,-1),(width,-3),(0,-3),(0,-1)])
        background=expand(path(coords))
        assert len(set(background))==len(background)-1
        assert cycle.isdisjoint(background)
        assert set(background)&terminal==terminal-{grid[(a,0)],grid[(b,0)]}

    first=arch(ts[0],ts[3],2);second=arch(ts[1],ts[5],-2)
    counts=verify(first,second)
    neutral_counts=verify([grid[(ts[0],1)]],arch(ts[0],ts[3],-2))
    neutral_pair=verify([grid[(0,0)]],[grid[(1,0)]])
    rank=len(basis([((1<<(m-2))-1)^(1<<i) for i in range(m-2)]))
    assert rank==m-2
    print('dual vertices/physical sites/physical vertices',V,len(edges),len(faces))
    print('disjoint-pair and robust single-pair geometry certificates',geometries,m*(m-1)//2)
    print('original support cardinalities for three jointly interpolated pairs',counts,neutral_counts,neutral_pair)
    print('rank on projected terminal quotient',rank)
    from dual_charge_moments import ChargeMoments
    moments=ChargeMoments(V,((a,b,int(i in tags)) for i,(a,b) in enumerate(edges)))
    def indexed_cut(vertices):
        chosen=set(vertices)
        return sum(1<<i for i,(a,b) in enumerate(edges) if (a in chosen)!=(b in chosen))
    yes=tuple(indexed_cut(vs) for vs in (first,second))
    no=tuple(indexed_cut(vs) for vs in (arch(ts[0],ts[1],2),arch(ts[1],ts[2],-2)))
    assert moments.pair(*yes)==(0,0) and moments.pair(*no)==(1,0)
    X,(matrix,unused)=moments.projected()
    assert len(X)==len(basis(matrix))==6 and not any(unused)
    print('computed charge moments on two indexed pairs',(0,0),(1,0))


if __name__=='__main__':
    replay()
