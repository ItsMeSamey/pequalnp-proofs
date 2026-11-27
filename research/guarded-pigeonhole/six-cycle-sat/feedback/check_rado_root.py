from itertools import permutations,product,combinations
from check_artificial_rebases import apply

def labels(p):
    lab={}
    for i in range(len(p)):
        j=i
        while j not in lab:
            lab[j]=i
            j=p[j]
    return lab

native=((0,1,2),(1,2,0))
fake=((1,0,2),(0,2,1),(2,1,0))
tested=roots=strict=0
example=None
for p in permutations(range(6)):
    native_masks=list(product(range(2),repeat=2))
    states=[labels(apply(p,m,native)) for m in native_masks]
    for f in product(range(3),repeat=2):
        ids=labels(apply(p,f,fake))
        vertices=set(ids.values())
        if min(len(set(s.values())) for s in states)!=len(vertices)-2:continue
        es=[]
        for g in range(2):
            for h in range(2):
                es.append(tuple(ids[3*g+i] for i in range(3) if fake[f[g]][i]!=native[h][i]))
        def partition(indices):
            blocks={v:v for v in vertices}
            for j in indices:
                x,y=es[j]
                a,b=blocks[x],blocks[y]
                for v in vertices:
                    if blocks[v]==a:blocks[v]=b
            return blocks
        spans=[]
        for m in native_masks:
            c=partition([m[0],2+m[1]])
            if len(set(c.values()))==len(vertices)-2:spans.append(c)
        if not spans:raise AssertionError()
        if len(spans)<4:
            strict+=1
            if example is None:example=(p,f,es)
        for a,b in product((-1,0,1),repeat=2):
            chosen=([a] if a>=0 else [])+([2+b] if b>=0 else [])
            c=partition(chosen)
            if len(set(c.values()))==len(vertices)-len(chosen):
                if not any(all(d[es[j][0]]==d[es[j][1]] for j in chosen) for d in spans):
                    raise AssertionError((p,f,chosen))
        for i,j in combinations(range(6),2):
            if any(d[ids[i]]==d[ids[j]] for d in spans)!=any(s[i]==s[j] for s in states):
                raise AssertionError((p,f,i,j))
            roots+=1
        tested+=1
print(tested,roots,strict,example)
