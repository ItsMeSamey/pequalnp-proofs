from itertools import product

def graph_connects(links):
    edges=[set()for _ in range(9)]
    for u,v,sg,gain in [(0,0,-1,0)]+links:
        for x in range(3):
            a,b=3*u+x,3*v+(sg*x+gain)%3
            edges[a].add(b);edges[b].add(a)
    visited={0};work=[0]
    while work:
        v=work.pop()
        for x in edges[v]-visited:visited.add(x);work.append(x)
    return 1 in visited

def plane(rows):
    active={r for r in rows}
    assert len(active)>=3
    repeat=next((r for r in rows if rows.count(r)>=2),rows[0])
    other=next(r for r in rows if r!=repeat)
    canon=[]
    for r in rows:
        canon.append(next((i,j)for i,j in product(range(3),repeat=2)if
            tuple((i*a+j*b)%3 for a,b in zip(repeat,other))==r))
    # Preserve each input's sign when choosing a canonical direction.
    tags=[]
    for a,b in canon:
        factor=a or b
        tags.append((a*factor%3,b*factor%3,factor))
    mixed=sum(a!=0 and b!=0 for a,b,_ in tags)
    quotas={1:1,2:1} if mixed%2 else {1:2,2:0}
    if not mixed%2 and sum(a and not b for a,b,_ in tags)<2:return None
    specs=[]
    for a,b,f in tags:
        if a and b:specs.append((1,2,-1 if b==1 else 1, f if b==1 else -f))
        else:
            h=1 if a else 2
            if quotas[h]:
                quotas[h]-=1
                specs.append((0,h,1,f))
            else:specs.append((h,h,-1,2*f))
    deg=[0]*3
    for u,v,_,_ in specs:deg[u]+=1;deg[v]+=1
    assert all(not d%2 for d in deg)
    target={tuple((r[0]*i+r[1]*j)%3 for r in rows)for i,j in product(range(3),repeat=2)}
    for word in product(range(3),repeat=len(rows)):
        links=[(u,v,sg,gain*t)for t,(u,v,sg,gain)in zip(word,specs)]
        assert graph_connects(links)==(word not in target)
    return len(target)

if __name__=='__main__':
    dirs=((1,0),(0,1),(1,1),(1,2))
    nrows=0;nwords=0
    for counts in product(range(3),repeat=4):
        if sum(bool(c)for c in counts)<3 or sum(counts)>6:continue
        rows=[r for r,c in zip(dirs,counts)for _ in range(c)]
        verdict=plane(rows)
        if counts==(1,1,1,1):assert verdict is None
        else:
            assert verdict==9;nrows+=1;nwords+=3**len(rows)
    print(nrows,'plane multiplicity profiles,',nwords,'complete words')
