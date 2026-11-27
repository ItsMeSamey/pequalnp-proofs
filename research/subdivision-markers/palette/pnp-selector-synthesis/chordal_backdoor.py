"""Strong chordal edge backdoor for full indexed cographic paired spaces."""
from collections import deque
from itertools import combinations
from three_part_vector import basis as chordal_basis


def minor(n,edges,selected,mask):
    parent=list(range(n))
    def root(v):
        while v!=parent[v]:
            parent[v]=parent[parent[v]];v=parent[v]
        return v
    omit=set(selected)
    for j,i in enumerate(selected):
        if mask>>j&1:
            u,v,_=edges[i];parent[root(u)]=root(v)
    classes={};image=[]
    for u in range(n):
        v=root(u)
        if v not in classes:classes[v]=len(classes)
        image.append(classes[v])
    charge=[0]*len(classes);links={}
    for i,(u,v,b) in enumerate(edges):
        a=image[u];c=image[v];charge[a]^=b;charge[c]^=b
        if i not in omit and a!=c:
            links.setdefault(tuple(sorted((a,c))),[]).append(i)
    return image,charge,links


def hole(size,links):
    adj=[set() for _ in range(size)]
    for a,b in links:adj[a].add(b);adj[b].add(a)
    for v,neighbors in enumerate(adj):
        for a,b in combinations(sorted(neighbors),2):
            if b in adj[a]:continue
            forbidden=(neighbors-{a,b})|{v}
            pred={a:None};todo=deque([a])
            while todo and b not in pred:
                x=todo.popleft()
                for y in adj[x]-forbidden:
                    if y not in pred:pred[y]=x;todo.append(y)
            if b in pred:
                cycle=[v,b]
                while cycle[-1]!=a:cycle.append(pred[cycle[-1]])
                return tuple(links[tuple(sorted((x,y)))] for x,y in zip(cycle,cycle[1:]+cycle[:1]))
    return ()


def discover(n,edges,k):
    edges=tuple(tuple(e) for e in edges)
    if k<0:raise ValueError("negative budget")
    memo=set()
    def search(s):
        if s in memo:return None
        memo.add(s)
        for mask in range(1<<len(s)):
            _,charges,links=minor(n,edges,s,mask)
            c=hole(len(charges),links)
            if c:
                if len(c)>k-len(s)+3:return None
                for bundles in combinations(c,len(c)-3):
                    added=[i for bundle in bundles for i in bundle]
                    if len(s)+len(added)>k:continue
                    result=search(tuple(sorted((*s,*added))))
                    if result is not None:return result
                return None
        return s
    return search(())


def leaf(image,charges,links,original,observation=None):
    size=len(charges);center=size
    pairs=list(links)
    adj=[[] for _ in range(size)]
    for i,(u,v) in enumerate(pairs):adj[u].append((v,i));adj[v].append((u,i))
    flow=[0]*len(pairs);sums=charges.copy();seen=set();roots=[];parents={};walk=[]
    for root in range(size):
        if root in seen:continue
        roots.append(root);todo=[root];seen.add(root)
        for u in todo:
            for v,i in adj[u]:
                if v not in seen:
                    seen.add(v);todo.append(v);parents[v]=(u,i)
        for v in reversed(todo[1:]):
            u,i=parents[v];flow[i]=sums[v];sums[u]^=sums[v]
        if sums[root]:return
        walk.extend(todo)
    extended=[(a,b,flow[i]) for i,(a,b) in enumerate(pairs)]
    for root in roots:
        parents[root]=(center,len(extended));extended.append((root,center,0))
    path={center:0}
    for v in walk:
        u,i=parents[v];path[v]=path[u]^(1<<i)
    projection=[path[image[a]]^path[image[b]] for a,b,_ in original]
    def original_cut(word):
        return sum(((word&row).bit_count()%2)<<i for i,row in enumerate(projection))
    pulled=None
    if observation is not None:
        pulled={}
        for (i,j),value in observation.items():
            if not value:continue
            left=projection[i]
            while left:
                u=left&-left;left^=u;right=projection[j]
                while right:
                    v=right&-right;right^=v
                    if u==v:continue
                    a,b=sorted((u.bit_length()-1,v.bit_length()-1))
                    pulled[a,b]=pulled.get((a,b),0)^value
        pulled={key:value for key,value in pulled.items() if value}
    for a,b,_ in chordal_basis(size+1,extended,observation=pulled):
        yield original_cut(a),original_cut(b)


def solve(n,edges,k,observation=None):
    """None outside budget, otherwise certified set and actual indexed witnesses."""
    edges=tuple(tuple(e) for e in edges)
    if n<1 or any(not(0<=u<n and 0<=v<n and 0<=b<4) for u,v,b in edges):
        raise ValueError("invalid input")
    s=discover(n,edges,k)
    if s is None:return None
    if observation is not None:
        observation=dict(observation)
        if any(not 0<=i<j<len(edges) or not isinstance(v,int) or v<0
               for (i,j),v in observation.items()):raise ValueError("invalid observation")
    def residue(word):
        for p in sorted(pivots,reverse=True):
            if word>>p&1:word^=pivots[p]
        return word
    pivots={};result=[]
    for mask in range(1<<len(s)):
        im,q,links=minor(n,edges,s,mask)
        reduced=None if observation is None else {ij:residue(v) for ij,v in observation.items()}
        if reduced is not None and not any(reduced.values()):break
        for a,b in leaf(im,q,links,edges,reduced):
            if observation is None:
                word=sum(((((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1)<<p
                         for p,(i,j) in enumerate(combinations(range(len(edges)),2)))
            else:
                word=0
                for (i,j),v in observation.items():
                    if (((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1:word^=v
            while word:
                p=word.bit_length()-1
                if p not in pivots:
                    pivots[p]=word;result.append((a,b));break
                word^=pivots[p]
    return s,result
