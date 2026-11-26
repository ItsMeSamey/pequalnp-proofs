"""Check the complete gauge barrier without using the split-clone solver."""
from itertools import product
cases=[
    ([56,120,64,3,3,3,6],[1,3,2,6,2,6,4],51,7,7,True),
    ([72,56,120,7,6,6,5],[1,2,1,2,6,6,2],31,5,1,False)]
for G,L,N,z,s,yes in cases:
    n=len(G);left=7;upper=[]
    for h in range(8):
        U=[set() for _ in range(4)]
        for x in range(1<<n):
            bad=0;score=0
            for i,row in enumerate(G):
                if x>>i&1:
                    bad|=((x&row).bit_count()%2)<<i
                    score^=L[i]^(h if N>>i&1 else 0)
            for j,mask in enumerate([0,N&left,N&~left,N]):
                if bad==(x&mask):U[j].add(score)
        visible={a for a,p,q in product(range(8),repeat=3) if p not in U[1] and q not in U[2] and a^p^q not in U[0]}
        assert not visible
        if h==0:assert z not in U[0]
        assert (s in U[3])==yes
        upper.append(U[3])
    assert all(x==upper[0] for x in upper)
    print('active target',s,'attained',yes,'all 8 gauges have empty visible set; active image',sorted(upper[0]))
