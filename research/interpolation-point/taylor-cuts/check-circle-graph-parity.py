"""Compare chord-set enumeration, cyclic bits and literal perfect matchings."""
from functools import cache
from random import Random


def words(n):
    def pair(items):
        if not items:
            yield []
            return
        for j in range(1,len(items)):
            for others in pair(items[1:j]+items[j+1:]):
                yield [(items[0],items[j])] + others
    for pairs in pair(list(range(2*n))):
        word=[None]*(2*n)
        for i,(x,y) in enumerate(pairs):
            word[x]=word[y]=i
        yield word


def check(word, marks, labels, matching=True):
    n=len(labels)
    visits=[[i for i,j in enumerate(word) if j==v] for v in range(n)]
    adj=[sum(1<<j for j,(l,r) in enumerate(visits) if
             ((l<x<r)^(l<y<r))) for x,y in visits]
    direct={}
    for s in range(1<<n):
        if all(not (s>>v&1) or (adj[v]&s).bit_count()%2==(marks>>v&1) for v in range(n)):
            lab=0
            for v in range(n):
                if s>>v&1:lab^=labels[v]
            direct[s]=lab
    arc_rank=[0]*n
    arc_labs=[0]*(2*n)
    signs=[]
    for j,v in enumerate(word):
        sign= -1 if (marks>>v&1) and arc_rank[v] else 1
        signs.extend((-sign,sign))
        if not arc_rank[v]:
            arc_labs[j-1]^=labels[v]
            arc_labs[j]^=labels[v]
        arc_rank[v]+=1
    actual={}
    for f in range(1<<(2*n)):
        fs=[(f>>j)&1 for j in range(2*n)]
        diff=[v-fs[j-1] for j,v in enumerate(fs)]
        if any(diff[x]+(-1 if marks>>v&1 else 1)*diff[y]
               for v,(x,y) in enumerate(visits)):
            continue
        s=sum((diff[x]!=0)<<v for v,(x,y) in enumerate(visits))
        lab=0
        for j,k in enumerate(arc_labs):
            if fs[j]:lab^=k
        assert direct[s]==lab
        actual[s]=actual.get(s,0)+1
    assert all(actual.get(s,0)==2 for s in direct)
    if not matching:return

    edges=[]
    offset=0
    next_id=6*n
    for j in range(2*n):
        e=2*j+1; g=2*((j+1)%(2*n))
        for u in (e,g):
            c=arc_labs[j] if u==e else 0
            if u==e and signs[u]<0:offset^=c
            v=word[u//2]
            for h in range(2):
                edges.append((u,4*n+2*v+h,c))
        if signs[e]==signs[g]:edges.append((e,g,0))
        else:
            edges.extend([(e,next_id,0),(g,next_id,0)])
            next_id+=1
    neigh=[[] for _ in range(next_id)]
    for i,j,w in edges:
        neigh[i].append((j,w));neigh[j].append((i,w))
    @cache
    def sums(mask):
        if not mask:return (1,)*1+(0,)*7
        vertices=[i for i in range(next_id) if mask>>i&1]
        i=min(vertices,key=lambda u:sum(mask>>v&1 for v,_ in neigh[u]))
        hist=[0]*8
        for j,w in neigh[i]:
            if mask>>j&1:
                rest=sums(mask^(1<<i)^(1<<j))
                for x,k in enumerate(rest):hist[x^w]+=k
        return tuple(hist)
    hist=sums((1<<next_id)-1)
    expected=[0]*8
    for lab in direct.values():expected[lab^offset]+=2**(n+1)
    assert tuple(expected)==hist


def main():
    rng=Random(55418)
    instances=0
    with_matching=0
    for n in range(1,5):
        for word in words(n):
            for marks in range(1<<n):
                labels=[rng.randrange(8) for _ in range(n)]
                full=n<=3 or rng.randrange(32)==0
                check(word,marks,labels,full)
                instances+=1;with_matching+=full
    print(instances,"chord-word/mark instances;",with_matching,"complete matching histograms")


if __name__=='__main__':
    main()
