from itertools import permutations, product
from collections import Counter

def count(p):
    seen=set()
    k=0
    for i in range(len(p)):
        if i in seen:continue
        k+=1
        while i not in seen:
            seen.add(i)
            i=p[i]
    return k

def apply(p, choices, maps):
    return [p[i-i%3+maps[choices[i//3]][i%3]] for i in range(len(p))]

if __name__=='__main__':
    native=((0,1,2),(1,2,0))
    fake=((1,0,2),(0,2,1),(2,1,0))
    for n in (1,2,3):
        from random import Random
        rng=Random(338)
        cases=permutations(range(3*n)) if n<3 else [rng.sample(range(9),9) for _ in range(5000)]
        results=Counter()
        examples={}
        for p in cases:
            k=count(p)
            const=all(count(apply(p,h,native))==k for h in product(range(2),repeat=n))
            full=any(count(apply(p,h,fake))==k+n for h in product(range(3),repeat=n))
            results[const,full]+=1
            examples.setdefault((const,full,k),p)
        print(n,results)
        for key,p in sorted(examples.items()):
            if key[0]:
                print(key,p)

    from collections import defaultdict
    tested=joined=0
    for p in permutations(range(6)):
        masks=list(product(range(2),repeat=2))
        def orbit_map(perm):
            ids={}
            for i in range(len(perm)):
                j=i
                while j not in ids:
                    ids[j]=i
                    j=perm[j]
            return ids
        native_orbits=[orbit_map(apply(p,m,native)) for m in masks]
        k=count(p)
        const=all(len(set(o.values()))==k for o in native_orbits)
        for f in product(range(3),repeat=2):
            artificial=apply(p,f,fake)
            if count(artificial)!=k+2:continue
            ids=orbit_map(artificial)
            adj=defaultdict(list)
            for g in range(2):
                for mode in range(2):
                    changes=[3*g+i for i in range(3) if fake[f[g]][i]!=native[mode][i]]
                    x,y=map(ids.get,changes)
                    adj[x].append((y,g))
                    adj[y].append((x,g))
            def path(x,y,colors):
                if x==y:return True
                return any(g not in colors and path(z,y,colors|{g}) for z,g in adj[x])
            cyclic=any(path(v,w,{g}) for v in list(adj) for w,g in adj[v])
            if cyclic==const:raise AssertionError((p,f))
            tested+=1
            if const:
                for i in range(6):
                    for j in range(i+1,6):
                        if path(ids[i],ids[j],set())!=any(o[i]==o[j] for o in native_orbits):
                            raise AssertionError((p,f,i,j))
                        joined+=1
    print(tested,'maximum references checked;',joined,'root-pair comparisons')
