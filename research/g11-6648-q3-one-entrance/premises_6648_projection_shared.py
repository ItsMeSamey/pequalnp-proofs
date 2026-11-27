"""All allocated H batches must use the same two exceptional projected clauses."""
from premises_6648_projection import *
def atlas():
    universe=(1<<65536)-1
    def grid(left,right):
        row=sum(1<<s for s in right).to_bytes(32,'little')
        left=set(left)
        return int.from_bytes(b''.join(row if e in left else bytes(32) for e in range(256)),'little')
    def both(a):
        return grid(a,range(256)),grid(range(256),a)
    need=[both([s for s in range(256) if s&edge]) for edge in pairs]
    absent=[both([s for s in range(256) if not s&i]) for i in maxind]
    @lru_cache(None)
    def cov(r):
        if not r:return universe,universe
        a,b=cov(r&(r-1));x,y=need[(r&-r).bit_length()-1]
        return a&x,b&y
    return universe,grid,cov,absent
universe,grid,cov,absent=atlas()
def possible(U,k,exceptions=2):
    terms={0}|{1<<i for i in range(8)}
    for r in range(11):
        terms.add(sum(bit(b if a==r else a) for a,b in G if r in (a,b) and (a,b) not in {H[i] for i in range(len(H)) if U>>i&1}))
    guards={s for s in range(256) if any(s&~a==0 for a in terms)}
    joins={s|t for s in guards for t in guards}
    # An ancestor relation between exceptional supports can be oriented E -> F.
    rows=[]
    jr=sum(1<<s for s in joins)
    for e in range(256):
        row=jr if e in joins else 0
        if row: row |= sum(1<<s for s in {e|g for g in guards})
        rows.append(row.to_bytes(32,'little'))
    allow=int.from_bytes(b''.join(rows),'little')
    if exceptions==1:
        allow &= grid(joins,[0])
    @lru_cache(None)
    def good(r):
        miss=allmiss
        for s in guards:
            if not r&~C[s]:miss &= ~reject[s]
        ce,cf=cov(r)
        out=allow
        while miss and out:
            b=miss&-miss
            a,c=absent[b.bit_length()-1]
            out &= (ce&a)|(cf&c)
            miss-=b
        return out
    @lru_cache(None)
    def ways(r,n):
        if n==1:return good(r)
        out=good(r)
        if not r:return out
        s=(r-1)&r
        while s and out!=allow:
            if s&(r&-r):
                a=good(s)
                if a:out |= a & ways(r^s,n-1)
            s=(s-1)&r
        return out
    return bool(ways(U,k))
if __name__=='__main__':
    import sys
    lo,hi,k=map(int,sys.argv[1:4])
    exc=int(sys.argv[4]) if len(sys.argv)>4 else 2
    for n in range(lo,hi+1):
        bad=[u for u in range(1,2048) if u.bit_count()==n and possible(u,k,exc)]
        print(n,k,len(bad),next(iter(bad),None),flush=True)
