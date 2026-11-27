from itertools import combinations
from random import Random
from h5_terminal_prefix import finish

def brute(bank,p,n,hidden):
    # Every OR costs one. Explicitly allow arbitrary sharing of every new node.
    bank=[a|(b<<p)|((1<<(p+n)) if hidden and hidden[i] else 0) for i,(a,b) in enumerate(bank)]
    pos=(1<<p)-1; neg=((1<<n)-1)<<p; flag=1<<(p+n)
    start=frozenset(bank)
    frontier={start}
    seen={start}
    for cost in range(len(bank)+1):
        for state in frontier:
            for a,b in combinations(state,2):
                if a&b&pos==pos and not(a&b&neg) and (not hidden or a&b&flag):return cost
        nxt=set()
        for state in frontier:
            for a,b in combinations(state,2):
                c=a|b
                if c not in state:
                    new=state|{c}
                    if new not in seen:nxt.add(new)
        frontier=nxt
        seen.update(nxt)
    return None

def physical():
    # Two paid-for old ORs (ids 8,9) and five actual ANDs (ids 10..14).
    rows=[]
    for x in range(256):
        raw=[bool(x>>i&1) for i in range(8)]
        u=raw[0] or raw[1];v=raw[6] or raw[7]
        s=raw[2] and raw[3];t=raw[4] and raw[5]
        wires=raw+[u,v,s,t,u and raw[4],v and raw[2],u and raw[2]]
        rows.append((wires,(u or s) and (v or t)))
    pos=[x for x,(_,a) in enumerate(rows) if a and not any(rows[x^(1<<i)][1] for i in range(8) if x>>i&1)]
    neg=[x for x,(_,a) in enumerate(rows) if not a and all(rows[x|1<<i][1] for i in range(8) if not x>>i&1)]
    bank=[tuple(sum(1<<j for j,x in enumerate(S) if rows[x][0][i]) for S in (pos,neg)) for i in range(15)]
    ans=finish(bank,len(pos),len(neg),[i>=10 for i in range(15)])
    assert ans and ans[0]==2
    _,a,b=ans
    assert all((any(w[i] for i in a) and any(w[i] for i in b))==out for w,out in rows)
    return ans

if __name__=='__main__':
    rng=Random(815)
    cnt=0
    for _ in range(90):
        p=n=2;m=rng.randrange(2,5)
        bank=[(rng.randrange(1<<p),rng.randrange(1,1<<n)) for i in range(m)]
        for flags in [None,[bool(rng.randrange(2)) for i in range(m)]]:
            ans=finish(bank,p,n,flags)
            assert (None if ans is None else ans[0])==brute(bank,p,n,flags)
            cnt+=1
    hidden_only=finish([(1,1),(1,2),(0,1)],1,2,[False,True,True])
    assert hidden_only and hidden_only[0]==1
    print(cnt,physical(),hidden_only)
