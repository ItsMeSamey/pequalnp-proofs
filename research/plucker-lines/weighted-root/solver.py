"""GF(2) weights of induced cycles through a fixed edge, with optional isolated vertex."""
from collections import deque
from itertools import permutations


def bits(mask):
    while mask:
        one = mask & -mask
        yield one.bit_length() - 1
        mask ^= one


def path(adj, s, t, allowed):
    if not (allowed >> s & 1 and allowed >> t & 1):
        return 0
    prev = {s: None}
    q = deque([s])
    while q:
        i = q.popleft()
        if i == t:
            out = 0
            while i is not None:
                out |= 1 << i
                i = prev[i]
            return out
        for j in bits(adj[i] & allowed):
            if j not in prev:
                prev[j] = i
                q.append(j)
    return 0


def component(adj, start, allowed):
    seen = 0
    frontier = (1 << start) & allowed
    while frontier:
        seen |= frontier
        neighbors = 0
        for i in bits(frontier):
            neighbors |= adj[i]
        frontier = neighbors & allowed & ~seen
    return seen


def search(original, s, t, weights):
    """Return parity -> actual support. The input graph is simple and undirected."""
    n = len(original)
    real = (1 << n) - 1
    adj = list(original)
    if not (adj[s] >> t & 1):
        raise ValueError("specified edge is missing")
    adj[s] ^= 1 << t
    adj[t] ^= 1 << s
    base = path(adj,s,t,real)
    if not base:
        return {}
    for h in bits(weights):
        cycle = path(adj,s,t,real & ~((1 << h) | original[h]))
        if cycle:
            parity = (cycle & weights).bit_count() % 2
            return {parity:cycle, 1-parity:cycle | (1 << h)}

    # Five-vertex tails keep the first/last anchor three steps from the original terminals.
    adj += [0] * 10
    left = list(range(n,n+5)) + [s]
    right = [t] + list(range(n+5,n+10))
    for chain in [left,right]:
        for i,j in zip(chain,chain[1:]):
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    first = tuple(left[1:4])
    last = tuple(right[2:5])
    allv = (1 << len(adj))-1
    candidates = {}
    for u in list(bits(weights)) + [first[1],last[1]]:
        allowed = allv & ~((1 << u) | adj[u])
        near = component(adj,left[0],allowed)
        far = component(adj,right[-1],allowed)
        assert not (near & far)
        choices = [(a,u,b) for a,b in permutations(bits(adj[u]),2) if not (adj[a] >> b & 1)]
        if u==first[1]:
            choices = [first]
        if u==last[1]:
            choices = [last]
        for frame in choices:
            candidates[frame] = (near,far)
    ordered = sorted(candidates,key=lambda f:candidates[f][0].bit_count())
    solutions = {first:{0:0}}
    for prev in ordered:
        if prev not in solutions or prev == last:
            continue
        a,u,b = prev
        _,far = candidates[prev]
        startmask = sum(1 << i for i in prev)
        for nxt in ordered:
            c,v,d = nxt
            near,_ = candidates[nxt]
            endmask = sum(1 << i for i in nxt)
            if startmask & ~near or endmask & ~far:
                continue
            both = near & far
            for r in bits(adj[b]&far):
                if r!=c and (not (both >> r & 1) or weights >> c & 1):
                    continue
                seq = [a,u,b,r] + ([c] if r!=c else []) + [v,d]
                if len(set(seq)) != len(seq):
                    continue
                # Fixed frame may have a gap only between r and c.
                if any(adj[x] >> y & 1 for k,x in enumerate(seq) for y in seq[k+2:]):
                    continue
                frame = startmask | endmask | (1 << r)
                if r == c:
                    middle = 1 << r
                else:
                    banned = frame | weights
                    for x in (a,u,b,v,d):
                        banned |= adj[x]
                    allowed = (both & ~banned) | (1 << r) | (1 << c)
                    middle = path(adj,r,c,allowed)
                    if not middle:
                        continue
                arc = (weights & ((1 << u) | (1 << b) | (1 << r))).bit_count() % 2
                store = solutions.setdefault(nxt,{})
                for old,sel in solutions[prev].items():
                    store.setdefault(old^arc,sel | frame | middle)
    return {w:sel & real for w,sel in solutions.get(last,{}).items()}


def affine_basis(adj,s,t):
    """Return affinely independent actual supports spanning all cycle/spectator supports."""
    initial=search(adj,s,t,0)
    if not initial:
        return []
    base=initial[0]
    result=[base]
    pivots={}
    n=len(adj)
    while True:
        changed=False
        for free in range(n):
            if free in pivots:
                continue
            w=1<<free
            # Each pivot is the highest set bit of its equation.
            for i in sorted(pivots):
                if (w & pivots[i]).bit_count()%2:
                    w|=1<<i
            other=1-(w & base).bit_count()%2
            candidate=search(adj,s,t,w).get(other)
            if candidate is None:
                continue
            row=candidate^base
            while row and row.bit_length()-1 in pivots:
                row^=pivots[row.bit_length()-1]
            assert row
            pivots[row.bit_length()-1]=row
            result.append(candidate)
            changed=True
            break
        if not changed:
            return result
