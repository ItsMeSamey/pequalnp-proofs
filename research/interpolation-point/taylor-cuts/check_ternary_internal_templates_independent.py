"""Check the template expansion by exhaustive edge-labelled matching replay."""
from itertools import combinations,product
from random import Random


def matchings(vertices,edges,chosen=()):
    if not vertices:
        yield chosen
        return
    u=min(vertices)
    for i,(p,q,w) in enumerate(edges):
        if u not in (p,q):
            continue
        v=q if u==p else p
        if v in vertices:
            yield from matchings(vertices-{u,v},edges,chosen+(i,))


def check(n,left,templates,cross):
    def plus(a,b):
        return tuple((x+y)%3 for x,y in zip(a,b))
    original=list(cross)
    map_id={}
    for k,(side,a,b,offset) in enumerate(templates):
        for u,v in product(a,b):
            if u!=v:
                value=plus(plus(a[u],b[v]),offset)
                map_id[k,u,v]=len(original)
                original.append((u,v,value))
    def gain(edges,ids):
        return tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(2))
    all_ids=list(matchings(set(range(n)),original))
    target={gain(original,ids) for ids in all_ids}
    found=set()
    for mult in product(range(n//2+1),repeat=len(templates)):
        if sum(mult)>n//2:
            continue
        p=sum(z for z,t in zip(mult,templates) if t[0]==0)
        if 2*(2*p-sum(mult))!=2*left-n:
            continue
        edges=list(cross)
        tag={i:("cross",i) for i in range(len(edges))}
        size=n
        for k,((side,a,b,offset),z) in enumerate(zip(templates,mult)):
            for _ in range(z):
                for slot,mapping in enumerate((a,b)):
                    for u,w in mapping.items():
                        tag[len(edges)]=(size,k,slot,u)
                        edges.append((u,size+slot,plus(w,offset) if slot==0 else w))
                size+=2
        for ids in matchings(set(range(size)),edges):
            reconstructed=[]
            slots={}
            for i in ids:
                t=tag[i]
                if t[0]=="cross":
                    reconstructed.append(t[1])
                else:
                    key,k,slot,u=t
                    slots.setdefault((key,k),{})[slot]=u
            for (_,k),by_slot in slots.items():
                reconstructed.append(map_id[k,by_slot[0],by_slot[1]])
            assert sorted(v for i in reconstructed for v in original[i][:2])==list(range(n))
            assert gain(original,reconstructed)==gain(edges,ids)
            found.add(gain(edges,ids))
    assert found==target


if __name__=="__main__":
    rng=Random(70135)
    for _ in range(200):
        n=rng.choice((0,2,4,6))
        left=rng.randrange(n+1)
        cuts=(range(left),range(left,n))
        def weight():
            return tuple(rng.randrange(3) for _ in range(2))
        cross=[(u,v,weight()) for u,v in product(*cuts) if rng.randrange(2)]
        templates=[]
        for k in range(rng.randrange(4)):
            side=rng.randrange(2)
            a,b=({u:weight() for u in cuts[side] if rng.randrange(3)} for _ in range(2))
            templates.append((side,a,b,weight()))
        check(n,left,templates,cross)
    print("200 cut/template multigraphs: exact target sets and every lifted matching witness passed")
