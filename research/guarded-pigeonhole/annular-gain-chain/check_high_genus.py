from itertools import combinations,product
from collections import defaultdict,Counter
import random
from check import test_path
from check_native_masks import orbit_labels,route,arm_gains

def cycles(black):
    at=defaultdict(lambda:defaultdict(list))
    for i,d in enumerate(black):at[i//3][d].append(i)
    for h in at:
        for ar in at[h].values():yield from combinations(ar,2)
    for h,k in combinations(at,2):
        for d,e in combinations(at[h].keys()&at[k].keys(),2):
            yield from product(at[h][d],at[h][e],at[k][d],at[k][e])

def chart(sigma):
    n=len(sigma);g=n//3
    disks,B=orbit_labels(sigma);faces,F=orbit_labels(route(sigma,2**g-1))
    dual=defaultdict(list)
    for a in range(n):
        u,v=faces[a],faces[sigma[a]]
        dual[u].append((v,a));dual[v].append((u,a))
    for cy in cycles(disks):
        reach={0};todo=[0]
        while todo:
            for v,a in dual[todo.pop()]:
                if a not in cy and v not in reach:reach.add(v);todo.append(v)
        if len(reach)==F:return None
    states=[orbit_labels(route(sigma,m))[0] for m in range(2**g)]
    gains={}
    result=Counter()
    for a,b in combinations(range(n),2):
        key=tuple(sorted((faces[a],faces[b])))
        if key not in gains:
            bits=arm_gains(dual,*key);ss=[]
            for i in range(g):
                row={};ok=True
                for j in range(3*i,3*i+3):
                    d=disks[j];value=int(j in bits)
                    if d in row and row[d]!=value:ok=False
                    row[d]=value
                if ok:ss.append(row)
            gains[key]=ss
        predicted=disks[a]==disks[b] or test_path(gains[key],disks[a],disks[b])
        actual=any(r[a]==r[b] for r in states)
        assert predicted==actual,(sigma,a,b)
        result[actual]+=1
    genus=(2-(B+g+F-n))//2
    return genus,result

def heawood(rng):
    perm=[None]*21
    for d in range(7):
        arms=[3*h+i for h in range(7) for i,k in enumerate([0,1,3]) if (h+k)%7==d]
        rng.shuffle(arms)
        for a,b in zip(arms,arms[1:]+arms[:1]):perm[a]=b
    return perm

def splice(s,t,i,j):
    k=len(s);a=s+[k+x for x in t]
    a[i],a[k+j]=a[k+j],a[i]
    return a

rng=random.Random(140);genera=Counter();counts=Counter()
for _ in range(15):
    h=heawood(rng)
    for chartperm in [h,splice([1,0,2],h,rng.randrange(3),rng.randrange(21))]:
        g,r=chart(chartperm);assert g>0
        genera[g]+=1;counts.update(r)
print('genera',genera,'pairs',counts)
assert counts[False]>0
