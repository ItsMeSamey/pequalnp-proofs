"""Single-chord pair of hosts, an exact base check and width-seven window checks."""
BASE=[22,41,1,2,97,722,176,352,11904,1312,2816,5376,26624,20736,45056,16384]
BAGS=[{11,12,13,14,15},{8,11,12,13,15},{7,8,9,10,11},{5,7,8,9},set(range(8))]
def edge(rows,i,j):
    assert i!=j and not rows[i]>>j&1 and not rows[j]>>i&1
    rows[i]|=1<<j
    rows[j]|=1<<i

def instance(w):
    assert w>=1
    good=BASE.copy()
    a,b=15,12
    bags=BAGS[:2]
    for _ in range(w):
        u,v=len(good),len(good)+1
        good.extend([0,0])
        edge(good,a,b);edge(good,a,u);edge(good,b,v)
        bags.append({8,11,a,b,u,v})
        a,b=u,v
    bags+=BAGS[2:]
    bad=good.copy()
    edge(bad,10,13)
    return good,bad,(a,b),bags

def check(w):
    g,h,pins,bags=instance(w)
    n=len(g)
    assert max(map(len,bags))==8 and max(x.bit_count() for x in h)==5
    assert len(set(map(frozenset,bags)))==len(bags)
    occ=[[j for j,B in enumerate(bags) if i in B] for i in range(n)]
    assert all(js==list(range(js[0],js[-1]+1)) for js in occ)
    for i,row in enumerate(g):
        assert row.bit_count()%2==1
        for j in range(i):
            if row>>j&1: assert set(occ[i])&set(occ[j])
    for start in range(len(bags)-w+1):
        mask=sum(1<<i for i in set.union(*bags[start:start+w]))
        assert all((g[i]^h[i])&mask==0 for i in range(n) if mask>>i&1)
    return n,pins,len(bags),min(abs(i-j) for i in occ[10] for j in occ[13])

def witnesses(rows,pins):
    p=sum(1<<v for v in pins)
    return [s for s in range(1<<len(rows)) if s&p==p and
            all(not s>>i&1 or (s&r).bit_count()%2 for i,r in enumerate(rows))]

if __name__=='__main__':
    h=BASE.copy();edge(h,10,13)
    assert witnesses(BASE,(15,12))==[65535] and witnesses(h,(15,12))==[]
    for k in [1,2,3,5,8,13,21]:
        print(k,check(k))
    g,h,p,_=instance(1)
    assert witnesses(g,p)==[(1<<len(g))-1] and not witnesses(h,p)
