"""Build actual layered binary programs and count undirected enabled components."""
from itertools import product
from collections import Counter

def build(w,side):
    blocks=[(j,j.bit_length()) for j in range(2,w+1)]
    pos=0
    root,reject,start=0,1,2
    nodes=3
    arcs=[(start,root,None,1)]
    layer={(0,0,0,1,0):start}
    for j,width in blocks:
        leaf=nodes
        nodes+=1
        for i in range(width):
            nxt={}
            arcs.append((leaf,root,pos,1))
            for (h,o,bad,zero,cmp),u in layer.items():
                for bit in (0,1):
                    z=zero and not bit
                    limit=(j>>(width-1-i))&1
                    c=cmp or ((bit>limit)-(bit<limit))
                    state=(h,o,bad,z,c)
                    if i==width-1:
                        state=(h^z,o^(not z and c<=0),bad or c>0,1,0)
                    if j==w and i==width-1:
                        hh,oo,bb,_,_=state
                        accept=(hh==0) if bb else (oo==side)
                        v=root if accept else reject
                    else:
                        if state not in nxt:
                            nxt[state]=nodes
                            nodes+=1
                        v=nxt[state]
                    arcs.append((u,v,pos,bit))
            layer=nxt
            pos+=1
    return nodes,arcs,pos

def excess(nodes,arcs,x):
    parent=list(range(nodes))
    def find(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]]
            i=parent[i]
        return i
    for u,v,i,b in arcs:
        if i is None or x[i]==b:
            parent[find(u)]=find(v)
    return len({find(i) for i in range(nodes)})-1

for w in (2,3,4):
    plus,minus=[build(w,s) for s in (0,1)]
    hist=[Counter(),Counter()]
    for x in product((0,1),repeat=plus[2]):
        for k,(n,edges,_) in enumerate((plus,minus)):
            hist[k][excess(n,edges,x)]+=1
    d=[1]
    for j in range(1,w+1):
        d=[p-j*q for p,q in zip([0]+d,d+[0])]
    assert all(hist[0][i]-hist[1][i]==d[i] for i in range(w+1))
    if w%2==0:
        assert set(hist[1])==set(range(1,w,2))
    print(w,plus[2],plus[0],len(plus[1]),dict(hist[0]),dict(hist[1]))
