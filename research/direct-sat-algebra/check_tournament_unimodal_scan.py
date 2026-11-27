"""Compare the three-parity two-arm scan with enumeration, including SCC blocks."""
from random import Random
from check_tournament_module_table import tournament, homogeneous

def verify(cuts, peak, blocks, rng, diagonal=None):
    a=len(cuts)
    groups=[]
    n=a
    for rows in blocks:
        groups.append(tuple(range(n,n+len(rows))))
        n+=len(rows)
    ins=[0]*n
    for j in range(a):
        ins[j]=(1<<j)-1
    for j,(group,rows) in enumerate(zip(groups,blocks)):
        mask=sum(1<<v for v in group)
        old=sum(1<<v for g in groups[:j] for v in g)
        for i,c in enumerate(cuts):
            if j<c:
                ins[i]|=mask
            else:
                old|=1<<i
        for i,v in enumerate(group):
            ins[v]=old | sum(1<<u for t,u in enumerate(group) if rows[t]>>i&1)
    d=rng.getrandbits(n) if diagonal is None else diagonal
    scan=[]
    for j in range(len(groups)+1):
        scan.extend(('a',i) for i in range(peak+1) if cuts[i]==j)
        scan.extend(('r',i) for i in reversed(range(peak+1,a)) if cuts[i]==j)
        if j<len(groups):scan.append(('b',j))
    for tau in (0,1):
        reachable={(0,0,0)}
        for tag,i in scan:
            nxt=set(reachable)
            for l,r,b in reachable:
                if tag=='b':
                    local=sum(((d>>v)&1)<<t for t,v in enumerate(groups[i]))
                    if ((l^r^b),1,0) in homogeneous(blocks[i],local,0):
                        nxt.add((l,r,b^1))
                elif tag=='a' and (l^b)==(d>>i&1):
                    nxt.add((l^1,r,b))
                elif tag=='r' and (r^b^tau^1)==(d>>i&1):
                    nxt.add((l,r^1,b))
            reachable=nxt
        got={b for l,r,b in reachable if l^r==tau}
        expected=set()
        for x in range(1<<n):
            if ((x&((1<<a)-1)).bit_count()%2==tau and all(not(x>>i&1) or
                    (row&x).bit_count()%2==(d>>i&1) for i,row in enumerate(ins))):
                expected.add((x>>a).bit_count()%2)
        assert got==expected

if __name__=='__main__':
    rng=Random(17305)
    for _ in range(300):
        a=rng.randrange(1,6)
        length=rng.randrange(1,5)
        peak=rng.randrange(a)
        cuts=sorted([rng.randrange(length+1) for _ in range(peak)])+[length]
        cuts+=sorted([rng.randrange(length+1) for _ in range(a-peak-1)],reverse=True)
        blocks=[tournament(n,rng.getrandbits(n*(n-1)//2))
                for n in (rng.randrange(1,4) for _ in range(length))]
        verify(cuts,peak,blocks,rng)
    print("300 mixed tournaments, both terminal mark and population parities passed")
