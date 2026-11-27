"""Original-label all-odd-pair search with local triangle/square degree conditions."""
from collections import deque
from itertools import combinations
from quartic_window_solver import WINDOW, compatible, extract, sites, valid, word_mask


def recognize(rows):
    """O(n^4) adjacency-index operations, counting all square cyclic orders."""
    n=len(rows)
    high={i for i,r in enumerate(rows) if r.bit_count()>4}
    if not high:
        return True
    adj=[]
    for row in rows:
        packed=row.to_bytes((n+7)//8,'little')
        adj.append(bytes((packed[j//8]>>(j%8))&1 for j in range(n)))
    for x in high:
        if any(adj[i][j] for i,j in combinations(sites(rows[x]),2)):
            return False
    def squares():
        for a,b,c,d in combinations(range(n),4):
            for u,v,w in ((b,c,d),(b,d,c),(c,b,d)):
                if adj[a][u] and adj[u][v] and adj[v][w] and adj[w][a]:
                    yield a,u,v,w
    counts=[bytearray(n) for _ in rows]
    for a,b,c,d in squares():
        for i,j in ((a,b),(b,c),(c,d),(d,a)):
            counts[i][j]=counts[j][i]=min(3,counts[i][j]+1)
    for sq in squares():
        if any(v in high for v in sq) and any(counts[v][sq[k-1]]==3 for k,v in enumerate(sq)):
            return False
    return True


def fold(rows,p,q):
    # Identical open OR closed neighborhoods. A pair selected together can be
    # deleted; if just the erased optional site was selected, swap to the keeper.
    active=(1<<len(rows))-1
    while True:
        open_seen={}
        closed_seen={}
        for v in sites(active & ~(1<<p|1<<q)):
            neighbors=rows[v]&active
            closed=neighbors | (1<<v)
            if neighbors in open_seen or closed in closed_seen:
                active ^= 1<<v
                break
            open_seen[neighbors]=closed_seen[closed]=v
        else:
            break
    ids=list(sites(active))
    reduced=[sum(((rows[v]>>old)&1)<<i for i,old in enumerate(ids)) for v in ids]
    return reduced,ids


def repair(rows,path,cap,kind):
    answer,case=extract(rows,path,cap,kind)
    if case=='child claw':
        # Identify the first remote chord and explicitly check its triangle
        # saturation. The only degree bound used by the shared extractor is here.
        prefix=[]
        required=[]
        for i,(s,t) in enumerate(path):
            required.extend(((s,() if i==0 else (path[i-1][0],)),
                             (t,() if i==0 else (path[i-1][1],s))))
        s,t=path[-1]
        c,d=cap
        required.extend(((c,(s,) if kind=='edges' else (s,t)),(d,(t,) if kind=='edges' else (c,))))
        for v,need in required:
            if not compatible(rows,prefix,v,need):
                neighbors=list(sites(rows[v]))
                assert len(neighbors)==4 and any(rows[a]>>b&1 for a,b in combinations(neighbors,2))
                break
            prefix.append(v)
        else:
            raise AssertionError('missing remote chord')
    return answer


def search(rows,p,q):
    start=((p,q),)
    pred={start:None}
    queue=deque([start])
    while queue:
        state=queue.popleft()
        s,t=state[-1]
        recent=[v for pair in state for v in pair]
        for x in sites(rows[s]):
            for kind,needs,nexts in (('edges',(s,),rows[t]),('claw',(s,t),rows[x])):
                if compatible(rows,recent,x,needs):
                    for y in sites(nexts):
                        if compatible(rows,recent+[x],y,(t,) if kind=='edges' else (x,)):
                            path=[]
                            tail=state
                            while tail is not None:
                                path.append(tail[-1])
                                tail=pred[tail]
                            return repair(rows,path[::-1],(x,y),kind)
            if compatible(rows,recent,x,(s,)):
                for y in sites(rows[x]&rows[t]):
                    if compatible(rows,recent+[x],y,(t,x)):
                        child=(*state[-(WINDOW-1):],(x,y))
                        if child not in pred:
                            pred[child]=state
                            queue.append(child)
    return None


def solve(rows,p,q,fold_twins=True):
    """Return ('YES', original mask), ('NO',None), or ('UNKNOWN',None)."""
    orig=tuple(rows)
    n=len(orig)
    if any(type(i) is not int or not 0<=i<n for i in (p,q)) or p==q:
        raise ValueError('two distinct valid pins required')
    if any(type(r) is not int or r<0 or r.bit_length()>n or r>>i&1 for i,r in enumerate(orig)):
        raise ValueError('invalid simple adjacency row')
    if any(not orig[j]>>i&1 for i,r in enumerate(orig) for j in sites(r)):
        raise ValueError('asymmetric adjacency')
    rows,ids=fold(orig,p,q) if fold_twins else (orig,list(range(n)))
    p,q=ids.index(p),ids.index(q)
    def lift(w):
        v=word_mask(ids[i] for i in sites(w))
        assert valid(orig,list(sites(v))) and w>>p&w>>q&1
        return 'YES',v
    pair=(1<<p)|(1<<q)
    full=(1<<len(rows))-1
    for k in (0,2,4):
        for extra in combinations(sites(full^pair),k):
            word=(p,q)+extra
            if valid(rows,word):
                return lift(word_mask(word))
    if not recognize(rows):
        return 'UNKNOWN',None
    def branch(i,j,dead,discard):
        active=full&~(dead|discard)
        reduced=[r&active if active>>k&1 else 0 for k,r in enumerate(rows)]
        reduced[i]^=1<<j
        reduced[j]^=1<<i
        ans=search(reduced,i,j)
        return None if ans is None else lift(dead|ans)
    pr,qr=rows[p],rows[q]
    for u in sites(pr&~qr):
        for v in sites(rows[u]&qr&~pr):
            ans=branch(u,v,pair,(pr&~(1<<u))|(qr&~(1<<v)))
            if ans is not None:
                return ans
    for x,y in ((p,q),(q,p)):
        for c in sites(pr&qr):
            for u in sites(rows[c]&rows[y]&~rows[x]&~pair):
                ans=branch(y,u,1<<x|1<<c,(rows[x]&~(1<<c))|(rows[c]&~(pair|1<<u)))
                if ans is not None:
                    return ans
    return 'NO',None
