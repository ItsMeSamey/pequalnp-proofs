"""Compare with unrestricted enumeration of all original pinned subsets."""
from itertools import combinations
from random import Random
from high_pin_odd_pair import find


def test(rows,p,q):
    odd=[]
    good=[]
    for w in range(1<<len(rows)):
        if not (w>>p&1 and w>>q&1):
            continue
        degrees=[(row&w).bit_count() for i,row in enumerate(rows) if w>>i&1]
        if all(d%2 for d in degrees):
            if not any(v&w==v for v in odd):
                if max(degrees)<=5 and min((rows[i]&w).bit_count() for i in (p,q))>=3:
                    good.append(w)
            odd.append(w)
    graph=[[j for j in range(len(rows)) if row>>j&1] for row in rows]
    ans=find(graph,[p,q])
    assert ans['high_pin_minimal']==bool(good)
    if good:
        assert sum(1<<i for i in ans['witness']) in good
    elif rows[p]>>q&1:
        assert ans['witness']==[p,q]
    else:
        assert ans['unrestricted']=='UNKNOWN' and ans['witness'] is None


def main():
    rng=Random(671896)
    hosts=[([224,112,104,84,42,87,47,1],3,5),
           ([52,56,41,38,35,31],0,1),([196,248,185,230,134,14,11,31],0,1),
           ([2,1,8,4],0,2),([0,0],0,1),([2,1],0,1)]
    for rows,p,q in hosts:
        test(rows,p,q)
    for rows,p,q in hosts[:3]:
        n=len(rows)
        base=rows[:]+[0]*4
        for i,j in list(combinations([2,*range(n,n+4)],2))+[(p,n),(q,n+1)]:
            base[i]|=1<<j
            base[j]|=1<<i
        for _ in range(6):
            order=list(range(n+4))
            rng.shuffle(order)
            mapped=[sum(1<<j for j,b in enumerate(order) if base[a]>>b&1) for a in order]
            test(mapped,order.index(p),order.index(q))
    for n in (6,8,10):
        for _ in range(25):
            rows=[0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(3)==0:
                    rows[i]|=1<<j
                    rows[j]|=1<<i
            test(rows,*rng.sample(range(n),2))
    print("99 original-host comparisons passed")


if __name__=='__main__':
    main()
