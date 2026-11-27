"""Exact local-batch relaxation, H only. Two unanchored clauses may vary by batch."""
from itertools import combinations
from functools import lru_cache
verts=(0,1,2,4,5,8,9,10)
G=((0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9))
H=[(a,b) for a,b in G if a in verts and b in verts]
def bit(a): return 1<<verts.index(a) if a in verts else 0
pairs=[bit(a)|bit(b) for a,b in H]
C=[sum(1<<i for i,e in enumerate(pairs) if e&m) for m in range(256)]
ind=[m for m in range(256) if not any((m&e)==e for e in pairs)]
maxind=[m for m in ind if not any(m!=n and m&n==m for n in ind)]
reject=[sum(1<<k for k,m in enumerate(maxind) if not m&s) for s in range(256)]
allmiss=(1<<len(maxind))-1

def analysis(U,exception_count=2):
    centers=[sum(bit(b if a==r else a) for a,b in G if r in (a,b) and (a,b) not in {H[i] for i in range(len(H)) if U>>i&1}) for r in range(11)]
    terms=[1<<i for i in range(8)]+centers
    def contained(m,arms):return any(m&~s==0 for s in arms)
    guards=[s for s in range(1,256) if contained(s,terms)]
    joins2={a|b for a in terms for b in terms}
    joins3={a|b for a in joins2 for b in terms}
    raw2=[s for s in range(1,256) if contained(s,joins2)]
    raw3=[s for s in range(1,256) if contained(s,joins3)]
    @lru_cache(None)
    def valid(r):
        miss=allmiss
        for s in guards:
            if r&~C[s]==0:miss&=~reject[s]
        if not miss:return True
        if exception_count==0:return False
        if exception_count==1:return any(r&~C[s]==0 and reject[s]&miss==miss for s in raw2)
        e2={reject[s]&miss for s in raw2 if r&~C[s]==0}
        if any(a|b==miss for a in e2 for b in e2):return True
        return any(r&~C[s]==0 and reject[s]&miss==miss for s in raw3)
    @lru_cache(None)
    def batches(r):
        if not r:return 0
        if valid(r):return 1
        best=16
        s=(r-1)&r
        while s:
            if s&(r&-r) and valid(s):best=min(best,1+batches(r^s))
            s=(s-1)&r
        return best
    return batches(U)
if __name__=="__main__":
    import sys
    counts={}
    for U in range(1<<len(H)):
        if U.bit_count()<int(sys.argv[1]):continue
        k=analysis(U,int(sys.argv[2]) if len(sys.argv)>2 else 2);counts[k]=max(counts.get(k,0),U.bit_count())
    print(counts)
