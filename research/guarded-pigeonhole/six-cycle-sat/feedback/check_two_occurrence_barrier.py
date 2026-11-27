from itertools import combinations

def triple(n,a,b,c):
    p=list(range(n))
    p[a],p[b],p[c]=b,c,a
    return p

def check():
    gens=[triple(6,*s) for s in combinations(range(6),3)]
    gens += [[p.index(i) for i in range(6)] for p in gens]
    rigid=0
    for p in gens:
        for q in gens:
            t=[q[i] for i in p]
            moved={i for i in range(6) if t[i]!=i and t[t[i]]==i}
            if len(moved)>=4:
                used={i for i in range(6) if p[i]!=i or q[i]!=i}
                if used!=moved or len(used)!=4:raise AssertionError((p,q))
                rigid+=1
    changes=[]
    for s in range(4):
        t=list(range(4))
        for k,p in enumerate((triple(4,1,3,2),triple(4,0,2,3))):
            if s>>k&1:t=[p[i] for i in t]
        changes.append({i for i in range(4) if (i>=2)!=(t[i]>=2)})
    if changes!=[set(),{1,2},{0,3},{0,2}]:raise AssertionError(changes)
    print(len(gens)**2,'ordered products;',rigid,'double-transposition cases;',changes)

if __name__=='__main__':check()
