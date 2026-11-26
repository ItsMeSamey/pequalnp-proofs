from itertools import combinations
f=[2,6,0,7,8,9,5,1,3,11,10,4]
g=[(5,11,3),(6,5,8),(8,4,10),(0,11,9)]
n=len(f)
signature=[[] for _ in range(n*(1+len(g)))]
for mask in range(1<<len(g)):
    p=f[:]; phases=[p[:]]
    for i,(a,b,c) in enumerate(g):
        if mask>>i&1:p[a],p[b],p[c]=p[b],p[c],p[a]
        phases.append(p[:])
    label={}; count=0
    for a in range(n):
        if a in label:continue
        x=a;mass=0
        while x not in label:
            label[x]=count;mass^=3331>>x&1;x=p[x]
        assert mass
        count+=1
    assert count==3
    for j,h in enumerate(phases):
        for a in range(n):signature[j*n+a].append(label[h[a]])
types=set(map(tuple,signature))
assert not any(all(len(set(v))==3 for v in zip(*triple)) for triple in combinations(types,3))
print('16 masks, 48 odd-mass cycles; all 60 positions admit no protected triple')
