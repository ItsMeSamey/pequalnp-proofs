from itertools import permutations, combinations
def join(k,r,s,t):
    v=r
    while True:
        v=k[t.get(v,v)]
        if v==s:return True
        if v==r:return False

n=6; swapcount=triplecount=0
for order in permutations(range(1,n)):
    cyc=(0,)+order
    k=dict(zip(cyc,cyc[1:]+cyc[:1]))
    for r,s in combinations(range(n),2):
        i,j=cyc.index(r),cyc.index(s)
        side=set(cyc[i:j] if i<j else cyc[i:]+cyc[:j])
        for a,b in combinations(range(n),2):
            if join(k,r,s,{a:b,b:a}) != ((a in side)==(b in side)):raise AssertionError()
            swapcount+=1
        for t in combinations(range(n),3):
            for a,b,c in (t,(t[0],t[2],t[1])):
                proj=tuple(x for x in cyc if x in t)
                q=proj.index(a)
                reverse=proj[(q+1)%3]==c
                mixed=0<len(set(t)&side)<3
                if (not join(k,r,s,{a:b,b:c,c:a})) != (mixed and reverse):raise AssertionError()
                triplecount+=1
print(swapcount,'swap checks;',triplecount,'three-cycle checks')
