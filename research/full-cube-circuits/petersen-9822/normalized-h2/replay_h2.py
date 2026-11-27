"""Replay compact hidden-two matching hints. Run with Python 3 (without -O)."""
from functools import cache
from itertools import combinations, product
from pathlib import Path
import sys

E = [6,24,17,33,66,132,264,528,160,640,576,320,288]
def bits(x):
    return [i for i in range(x.bit_length()) if x >> i & 1]
def mask(flags):
    return sum(1 << i for i, flag in enumerate(flags) if flag)
def union(items):
    out = 0
    for item in items:
        out |= item
    return out
def minimal(items):
    kept = []
    for s in sorted(set(items), key=int.bit_count):
        if all(k & s != k for k in kept):
            kept.append(s)
    return sorted(kept)

inside = [mask((s&e)==e for e in E) for s in range(1024)]
N = [s for s in range(1024) if not inside[s] and all(inside[s|1<<i] for i in bits(1023^s))]
assert len(N)==16
hits = [mask(s&e for e in E) for s in range(1024)]
neg = [mask(s&n for n in N) for s in range(1024)]
trace = [e|(n<<13) for e,n in zip(hits,neg)]
pairs = [(inside[x|y], (1<<i)|(1<<j)) for (i,x),(j,y) in combinations(enumerate(N),2)]
quads = [q for q in combinations(range(13),4) if union(E[i] for i in q).bit_count()==8]
free = [1023 ^ union(N[i] for i in bits(f)) for f in range(65536)]
@cache
def covers(t):
    if not t:
        return [0]
    return minimal(c | 1<<v for v in bits(E[bits(t)[0]]) for c in covers(t & ~hits[1<<v]))

def first():
    hs=set()
    for a,b in combinations(range(1,1024),2):
        if a&b: continue
        h=trace[a]&trace[b]
        he, hn=h&8191,h>>13
        if hn and all(he&~hits[1<<v] for v in range(10)) and any(not(e&~he or f&hn) for e,f in pairs):
            hs.add(h)
    assert len(hs)==5464
    best=minimal(h^8191 for h in hs)
    return sorted(h^8191 for h in best)

def replay(path):
    data=iter(path.read_bytes())
    counts=[0,0,0,0]
    for h in first():
        counts[0]+=1
        he,hn=h&8191,h>>13
        negatives=[neg[1<<v] for v in range(10)] + [hn]
        @cache
        def feasible(s):
            t,f=s&8191,s>>13
            for b in covers(t):
                bad=f&neg[b]
                can=hits[free[bad]&~b] | (0 if bad&hn else he)
                if not t&~can:
                    return True
            return False
        @cache
        def rescue(i,j):
            def labels(k):
                return bits(E[k])+([10] if he>>k&1 else [])+[11]
            opts=[]
            for a,b,c,d in product(labels(i),labels(j),labels(i),labels(j)):
                ban=0
                for u,v in product((a,b),(c,d)):
                    if u==v==11: break
                    if 11 in (u,v): ban|=negatives[min(u,v)]
                    elif negatives[u]&negatives[v]: break
                else:
                    t=((11 in (a,c))<<i)|((11 in (b,d))<<j)
                    opts.append(t|(ban<<13))
            return minimal(opts)
        visited=set()
        def verify(s):
            if s in visited: return
            visited.add(s)
            code=next(data)
            counts[2]+=1
            if code==255:
                assert s>>13==65535
                counts[3]+=1
                return
            assert code<len(quads)
            children=minimal(s|r for i,j in combinations(quads[code],2) for r in rescue(i,j) if feasible(s|r))
            assert s not in children
            for child in children: verify(child)
        roots=set()
        for vs in combinations(range(10),3):
            t=8191 & ~(hits[sum(1<<v for v in vs)] | (he&hits[free[hn]]))
            for cross in (False,True):
                for x in covers(t&~he if cross else t):
                    s=t|((neg[x]|(hn if cross else 0))<<13)
                    if feasible(s): roots.add(s)
        roots=minimal(roots)
        counts[1]+=len(roots)
        for s in roots: verify(s)
        feasible.cache_clear()
        rescue.cache_clear()
    assert next(data,None) is None and counts==[1035,2141,2239,1], counts
    print("verified first features, root demands, hint nodes, globally safe leaves",*counts)
if __name__=='__main__':
    if not __debug__: raise RuntimeError("assertions required")
    replay(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('h2-cover.bin'))
