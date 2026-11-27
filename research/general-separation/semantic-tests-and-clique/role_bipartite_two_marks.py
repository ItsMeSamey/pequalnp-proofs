"""Construct occupancies for the common-role 14-state network with two binary readouts."""
from collections import deque
from itertools import combinations
from random import Random


def bits(x):
    while x:
        b=x&-x
        yield b.bit_length()-1
        x^=b


def linear(labels,target):
    known={0:0}
    for i,k in enumerate(labels):
        for t,w in list(known.items()):
            known.setdefault(t^k,w|(1<<i))
    return known.get(target)


def mixed(rows,R,c,L):
    even=R&L&~c
    if even:
        return even&-even
    for s in bits(R&L&c):
        parent={s:None};queue=deque([s])
        while queue:
            i=queue.popleft()
            if (c&~L)>>i&1:
                path=1<<i
                while True:
                    i=parent[i]
                    path|=1<<i
                    if c>>i&1:
                        return path
            for j in bits(rows[i]&R):
                if j not in parent:
                    parent[j]=i
                    queue.append(j)
    return None


def solve(adj,deg,rows,c,labels,target):
    n=len(adj);total=len(rows);leaves=(1<<n)-1;hubs=((1<<total)-1)^leaves
    A=labels[:n];B=labels[n:]
    sol=linear(B,target)
    if sol is not None:return sol<<n
    col=0
    for b in B:col^=b
    sol=linear(A,target^col)
    if sol is not None:return hubs|sol
    if linear(labels,target) is None:return None
    # Any nonzero guarded column now has the same label, since rank two
    # on guarded columns would have permitted the all-hubs-on solution.
    tag=next(k for k in A if k)
    L=sum(1<<i for i,k in enumerate(A) if k)
    for i in bits(L):
        for j in bits(adj[i]):
            other=B[:j-n]+[0]+B[j-n+1:]
            sol=linear(other,target^tag^labels[j])
            if sol is not None:
                return (sol<<n)|(1<<j)|(1<<i)
    h=next(bits(adj[next(bits(L))]))
    assert all(adj[i]==1<<h for i in bits(L))
    R=sum(1<<i for i in range(n) if adj[i]==1<<h)
    baseline=hubs^(1<<h)
    for f in [baseline]+[baseline^(1<<j) for j in bits((leaves^R)|baseline)]:
        drift=c^deg
        for i in bits(R):
            drift^=((rows[i]&f).bit_count()%2)<<i
        sol=mixed(rows,R,drift,L)
        if sol is not None:return sol|f
    return None


def test():
    rng=Random(86173);count=0
    for n in range(1,6):
        for m in range(1,4):
            for _ in range(75):
                total=n+m;adj=[rng.randrange(1,1<<m)<<n for i in range(n)]
                if any(not any(v>>j&1 for v in adj) for j in range(n,total)):continue
                # An extra parallel edge changes degree parity without changing adj.
                deg=sum(((v.bit_count()%2)^rng.getrandbits(1))<<i for i,v in enumerate(adj))
                rows=[0]*total
                for i,j in combinations(range(total),2):
                    if rng.getrandbits(1):
                        rows[i]|=1<<j;rows[j]|=1<<i
                c=rng.randrange(1<<n);labels=[rng.randrange(4) for _ in rows]
                for t in range(4):
                    def valid(w):
                        lab=0
                        for i in bits(w):lab^=labels[i]
                        return lab==t and all(not(w>>i&1) or adj[i]&w or
                            (rows[i]&w).bit_count()%2==((c^deg)>>i&1) for i in range(n))
                    ans=solve(adj,deg,rows,c,labels,t)
                    assert (ans is not None)==any(valid(w) for w in range(1<<total))
                    assert ans is None or valid(ans)
                    count+=1
    print(count,"instances checked")


if __name__=="__main__":
    test()
