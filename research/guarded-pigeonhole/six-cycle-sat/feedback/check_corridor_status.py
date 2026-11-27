from itertools import permutations,product,combinations
from random import Random
from collections import defaultdict
from check_artificial_rebases import apply

def labels(p):
    d={}
    for i in range(len(p)):
        j=i
        while j not in d:
            d[j]=i
            j=p[j]
    return d

def classify(adj, marks):
    live={e for a in adj.values() for e in a}
    def incident(v):
        return [e for e in adj[v] if e in live]
    for _ in range(len(adj)):
        for v in adj:
            a=incident(v)
            if v not in marks and len(a)==1:live.remove(a[0])
    terminals=marks|{v for v in adj if len(incident(v))>=3}
    pins={e[0] for v in terminals for e in incident(v)}
    used=set()
    paths=[]
    for v in terminals:
        for e in incident(v):
            if e in used:continue
            path=[]
            w=v
            while True:
                used.add(e);path.append(e)
                w=e[1] if e[2]==w else e[2]
                if w in terminals:break
                e=next(f for f in incident(w) if f!=e)
            paths.append(path)
    return pins,paths

rng=Random(7)
fake=((1,0,2),(0,2,1),(2,1,0))
phys=((0,1,2),(1,2,0))
configs=pairs=0
for n in (1,2,3,4,5):
    for p in permutations(range(n*3)) if n<3 else [rng.sample(range(3*n),3*n) for _ in range(100)]:
        masks=list(product(range(2),repeat=n))
        state=[labels(apply(p,m,phys)) for m in masks]
        for b in (product(range(3),repeat=n) if n<3 else [rng.choices(range(3),k=n)]):
            lab=labels(apply(p,b,fake))
            adj=defaultdict(list)
            opts=[]
            for g in range(n):
                es=[]
                for h in phys:
                    x,y=sorted(lab[3*g+i] for i in range(3) if fake[b[g]][i]!=h[i])
                    e=(g,x,y)
                    if e not in es:adj[x].append(e);adj[y].append(e)
                    es.append(e)
                opts.append(es)
            chosen=[{opts[g][h] for g,h in enumerate(m)} for m in masks]
            configs+=1
            for r,s in combinations(range(3*n),2):
                pins,paths=classify(adj,{lab[r],lab[s]})
                table={}
                for m,c,t in zip(masks,chosen,state):
                    key=tuple(m[g] for g in sorted(pins))+tuple(all(e in c for e in path) for path in paths)
                    truth=t[r]==t[s]
                    if table.setdefault(key,truth)!=truth:raise AssertionError((p,b,r,s,m,key))
                pairs+=1
print(configs,'references;',pairs,'root pairs')
