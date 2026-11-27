"""Exhaust every normalized two-state target and candidate through six named inputs."""
from itertools import combinations,permutations
from collections import Counter

def project(p,S):
    out=[]
    for u in S:
        v=p[u]
        while v not in S:
            v=p[v]
        out.append(S.index(v))
    return tuple(out)

def profiles(m):
    perms=list(permutations(range(m)))
    out={p:0 for p in perms}
    for k in perms:
        for u,v in combinations(range(m),2):
            for p in perms:
                x=k[p[u]]
                while x not in (u,v):
                    x=k[p[x]]
                out[p]=2*out[p]+int(x==v)
    return out

def main():
    local={m:profiles(m) for m in (2,3,4)}
    for n in range(2,7):
        ps=list(permutations(range(n)))
        sets=[s for m in (2,3,4) for s in combinations(range(n),m)]
        lookup=[[local[len(s)][project(p,s)] for s in sets] for p in ps]
        sizes=Counter()
        for i,pi in enumerate(ps[1:],1):
            bounds=[a|b for a,b in zip(lookup[0],lookup[i])]
            survivors=[j for j,prof in enumerate(lookup) if all(x&~b==0 for x,b in zip(prof,bounds))]
            assert survivors==[0,i]
            assert any(a & ~b for a,b in zip(lookup[0],lookup[i]))
            assert any(b & ~a for a,b in zip(lookup[0],lookup[i]))
            sizes[len(survivors)]+=1
        print(n,sum(sizes.values()),'targets')
if __name__=='__main__':
    main()
