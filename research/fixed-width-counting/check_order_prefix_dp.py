from functools import cache
from itertools import permutations,product
from random import Random
rng=Random(81)
def test(blocks,order_edges):
    lab={i:l for block in blocks for i,l in block}
    parts=[frozenset(i for i,_ in block) for block in blocks]
    universe=frozenset(lab)
    @cache
    def bd(s):return {lab[i] for i in s}&{lab[i] for i in universe-s}
    preds={i:{a for a,b in order_edges if b==i} for i in range(len(blocks))}
    @cache
    def nexts(s):
        done={j for j,p in enumerate(parts) if p<=s}
        active=[j for j,p in enumerate(parts) if j not in done and p&s]
        if not active:active=[j for j in range(len(parts)) if j not in done and preds[j]<=done]
        return [s|{i} for j in active for i in parts[j]-s]
    @cache
    def reach(s):
        out={s}
        for t in nexts(s):out.update(reach(t))
        return out
    @cache
    def dp(s,t):
        if len(t-s)==1:return 1
        return min(max(dp(s,u),dp(u,t),len(bd(u-s)|bd(t-u))) for u in reach(s) if u!=s and u!=t and t in reach(u))
    got=dp(frozenset(),universe)
    best=len(universe)
    for bs in permutations(range(len(blocks))):
        if any(bs.index(a)>bs.index(b) for a,b in order_edges):continue
        for ls in product(*(permutations(parts[j]) for j in bs)):
            w=sum(ls,())
            @cache
            def ordered(i,j):
                if j-i==1:return 1
                return min(max(ordered(i,k),ordered(k,j),len(bd(frozenset(w[i:k]))|bd(frozenset(w[k:j])))) for k in range(i+1,j))
            best=min(best,ordered(0,len(w)))
    assert got==best
for case in range(80):
    k=rng.randrange(1,4)
    blocks=[];uid=0
    for j in range(k):
        block=[]
        for l in rng.sample(range(5),rng.randrange(1,4)):
            block.append((uid,l));uid+=1
        blocks.append(block)
    test(blocks,[(a,b) for b in range(k) for a in range(b) if rng.randrange(2)])
print("80 partially ordered block instances agree with exhaustive block and literal permutations")
