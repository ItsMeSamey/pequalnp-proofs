"""Audit tree-of-binary-space localization, allowing degenerate one-ports."""
from itertools import combinations, product
from random import Random


def reduce(x,basis):
    for pivot in sorted(basis,reverse=True):
        if (x>>pivot)&1:
            x ^= basis[pivot]
    return x


def basis(vectors):
    b={}
    for x in vectors:
        x=reduce(x,b)
        if x:
            b[x.bit_length()-1]=x
    return b


def total(vectors):
    x=0
    for v in vectors:
        x ^= v
    return x


def path(adj,a,b):
    prev={a:None}
    stack=[a]
    while stack:
        x=stack.pop()
        if x==b:
            break
        for y in adj[x]:
            if y not in prev:
                prev[y]=x
                stack.append(y)
    out=[]
    while b is not None:
        out.append(b)
        b=prev[b]
    return out


def run(rng,count):
    adj=[[] for _ in range(count)]
    widths=[rng.randrange(2,4) for _ in adj]
    starts=[sum(widths[:i]) for i in range(count)]
    real=[(i,rng.randrange(1<<widths[i])) for i in range(count)
          for _ in range(rng.randrange(1,3))]
    bridges=[]
    for i in range(1,count):
        j=rng.randrange(i)
        adj[i].append(j)
        adj[j].append(i)
        k=rng.choice([0,1,1,3])
        def virtual(v):
            if k==0:
                return []
            if k==1:
                return [rng.randrange(1<<widths[v])]
            a,b=rng.sample(range(1,1<<widths[v]),2)
            return [a,b,a^b]
        bridges.append((i,j,virtual(i),virtual(j)))
    glue=basis((x<<starts[i])^(y<<starts[j]) for i,j,aa,bb in bridges for x,y in zip(aa,bb))
    def embed(i,x):
        return reduce(x<<starts[i],glue)
    images=[embed(i,x) for i,x in real]
    local=[{x for j,x in real if j==i} for i in range(count)]
    virt=[set() for _ in adj]
    edge_labels={}
    for i,j,aa,bb in bridges:
        local[i].update(aa)
        local[j].update(bb)
        virt[i].update(aa)
        virt[j].update(bb)
        edge_labels[i,j]=set(embed(i,x) for x in aa)
        edge_labels[j,i]=edge_labels[i,j]
    killed=0
    for i in range(count):
        b=basis(x for x in virt[i] if not embed(i,x))
        for v in range(1<<widths[i]):
            assert (not embed(i,v)) == (not reduce(v,b))
        killed+=len(b)
    checked=0
    for a,b,c in combinations(range(len(real)),3):
        ids=(a,b,c)
        vs=[images[x] for x in ids]
        if not all(vs) or total(vs):
            continue
        loc=[real[x][0] for x in ids]
        med,=set(path(adj,loc[0],loc[1])) & set(path(adj,loc[0],loc[2])) & set(path(adj,loc[1],loc[2]))
        for idx,i in zip(ids,loc):
            if i!=med:
                branch=path(adj,i,med)[1]
                assert images[idx] in edge_labels[med,branch]
            assert images[idx] in {embed(med,x) for x in local[med]}
        checked+=1
    # Independent virtual-mask enumeration: XOR matching coefficients on each
    # virtual pair, collect all tuples of real-column sums feasible by these masks.
    boundary={(0,)*count}
    for i,j,aa,bb in bridges:
        for x,y in zip(aa,bb):
            shifted=set()
            for old in boundary:
                new=list(old)
                new[i]^=x
                new[j]^=y
                shifted.add(tuple(new))
            boundary.update(shifted)
    for selected in range(1<<len(real)):
        sums=[0]*count
        for k,(i,x) in enumerate(real):
            if (selected>>k)&1:
                sums[i]^=x
        assert (tuple(sums) in boundary) == (not total(images[k] for k in range(len(real)) if (selected>>k)&1))
    return checked,killed

if __name__=='__main__':
    rng=Random(712743)
    obs=[run(rng,rng.randrange(1,6)) for _ in range(600)]
    print('600 trees;',sum(a for a,b in obs),'median triangles;',sum(b for a,b in obs),'killed bag dimensions')
