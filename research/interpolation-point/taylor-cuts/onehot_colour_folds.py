"""Decision-only folds on a validated signed one-hot CNF+XOR graph presentation."""
from itertools import combinations,permutations
from collections import deque


def _parse(n,clauses,rows):
    """Return the validated local triples, signs, graph and edge bijections."""
    if type(n) is not int or n<0:raise ValueError("bad dimension")
    rows=list(dict.fromkeys(rows)); parts=[]; owner={}; rhs=[]
    for mask,b in rows:
        if type(mask) is not int or not 0<=mask<1<<n or b not in (0,1):raise ValueError("bad XOR row")
        if not mask and not b:continue
        vs=[i+1 for i in range(n) if mask>>i&1]
        if len(vs)!=3 or any(i in owner for i in vs):return None
        for i in vs:owner[i]=len(parts)
        parts.append(vs);rhs.append(b)
    signs={}; intern=[set() for _ in parts]; edges={}
    for c in clauses:
        if any(type(l) is not int or not 1<=abs(l)<=n for l in c):raise ValueError("bad literal")
        c=set(c)
        if any(-l in c for l in c):continue
        if len(c)!=2:return None
        a,b=sorted(c,key=abs); x,y=abs(a),abs(b)
        if x not in owner or y not in owner:return None
        if signs.setdefault(x,-a)!=-a or signs.setdefault(y,-b)!=-b:return None
        u,v=owner[x],owner[y]
        if u==v:intern[u].add((x,y));continue
        if u>v:u,v,x,y=v,u,y,x
        edges.setdefault((u,v),set()).add((x,y))
    for v,vs in enumerate(parts):
        if intern[v]!=set(combinations(vs,2)):return None
        if (rhs[v]^sum(signs[x]<0 for x in vs)%2)!=1:return None
    adj={v:set() for v in range(len(parts))};match={}
    for (u,v),pairs in edges.items():
        if len(pairs)!=3 or len(dict(pairs))!=3 or len({y for _,y in pairs})!=3:return None
        match[u,v]=dict(pairs);match[v,u]={y:x for x,y in pairs}
        adj[u].add(v);adj[v].add(u)
    return parts,signs,adj,match


def _synchronize(parts,adj,match):
    names={}
    for root in adj:
        if root in names:continue
        names[root]=tuple(parts[root]);stack=[root]
        while stack:
            u=stack.pop()
            for v in adj[u]:
                proposed=tuple(match[u,v][x] for x in names[u])
                if v in names:
                    if names[v]!=proposed:return None
                else:names[v]=proposed;stack.append(v)
    return names


def recognize(n,clauses,rows):
    parsed=_parse(n,clauses,rows)
    if parsed is None:return None
    parts,signs,adj,match=parsed
    names=_synchronize(parts,adj,match)
    if names is None:return None
    return [tuple(signs[x] for x in names[u]) for u in range(len(parts))],adj


def components(G,removed=()):
    left=set(G)-set(removed);parts=[]
    while left:
        root=min(left);left.remove(root);part={root};stack=[root]
        while stack:
            u=stack.pop();fresh=G[u]&left;left-=fresh;part|=fresh;stack.extend(fresh)
        parts.append(part)
    return parts


def bip(G):
    col={}
    for v in G:
        if v in col:continue
        col[v]=0;stack=[v]
        while stack:
            u=stack.pop()
            for x in G[u]:
                if x not in col:col[x]=1-col[u];stack.append(x)
                elif col[x]==col[u]:return None
    return col


def induced(G,S):
    return {v:G[v]&S for v in S}


def colour(G,*,max_nodes=256):
    if type(max_nodes) is not int or max_nodes<0:raise ValueError("bad node cap")
    stats={}; nodes=0
    def hit(key):stats[key]=stats.get(key,0)+1
    def part(G):
        nonlocal nodes
        if nodes>=max_nodes:return 'UNKNOWN',None
        nodes+=1; lifts=[]
        def finish(status,col=None):
            if status=='SAT':
                for u,vs,v in reversed(lifts):
                    col[u]=col[v] if v is not None else min({0,1,2}-{col[x] for x in vs})
            return status,col
        while True:
            c=bip(G)
            if c is not None:hit('bipartite');return finish('SAT',c)
            vertex=next((v for v in G if len(G[v])<=2),None)
            if vertex is not None:
                hit('degree_le_two');lifts.append((vertex,G[vertex],None))
                G=induced(G,set(G)-{vertex});continue
            for u in G:
                if bip(induced(G,G[u])) is None:
                    hit('odd_neighbourhood');return finish('UNSAT')
            pair=next(((u,v) for u in G for v in G if u!=v and G[u]<=G[v]),None)
            if pair:
                u,v=pair;hit('domination');lifts.append((u,(),v))
                G=induced(G,set(G)-{u});continue
            pair=None
            for u,v in combinations(G,2):
                if v not in G[u]:continue
                common=sorted(G[u]&G[v])
                if len(common)>=2:pair=common[:2];break
            if pair:
                u,v=pair
                if v in G[u]:hit('equal_adjacent');return finish('UNSAT')
                hit('diamond');lifts.append((u,(),v))
                neighbours=G[u]|G[v]
                G=induced(G,set(G)-{u})
                for t in neighbours:G[t].add(v);G[v].add(t)
                continue
            break
        # Two equal precolours create an available third colour at the last node.
        if max(map(len,G.values()))<=3:
            for root in G:
                for a,b in combinations(G[root],2):
                    if b in G[a] or len(components(G,(a,b)))!=1:continue
                    col={a:0,b:0};seen={root};queue=deque([root]);order=[]
                    while queue:
                        u=queue.popleft();order.append(u)
                        for v in sorted(G[u]-seen-{a,b}):seen.add(v);queue.append(v)
                    for u in reversed(order):
                        col[u]=min({0,1,2}-{col[x] for x in G[u] if x in col})
                    hit('subcubic_order');return finish('SAT',col)
        for k in range(4):
            for cut in combinations(G,k):
                if not all(v in G[u] for u,v in combinations(cut,2)):continue
                pieces=components(G,cut)
                if len(pieces)<2:continue
                hit('clique_cut');col={v:i for i,v in enumerate(cut)};unknown=False
                for S in pieces:
                    status,child=part(induced(G,S|set(cut)))
                    if status=='UNSAT':return finish('UNSAT')
                    if status=='UNKNOWN':unknown=True;continue
                    perm=next(p for p in permutations(range(3)) if all(p[child[v]]==col[v] for v in cut))
                    col.update({v:perm[c] for v,c in child.items()})
                return finish('UNKNOWN') if unknown else finish('SAT',col)
        hit('stalled');return finish('UNKNOWN')
    status,c=part(G);stats['nodes']=nodes
    return status,c,stats


def solve(n,clauses,xor_rows=(),*,max_nodes=256):
    clauses=tuple(tuple(c) for c in clauses);rows=tuple(tuple(r) for r in xor_rows)
    parsed=_parse(n,clauses,rows)
    if parsed is None:return 'UNKNOWN',None,{'unrecognized':1}
    parts,signs,G,matching=parsed
    names=_synchronize(parts,G,matching)
    removed=[]
    if names is None:
        while True:
            u=next((v for v in G if len(G[v])<=2),None)
            if u is None:break
            removed.append((u,tuple(G[u])))
            G=induced(G,set(G)-{u})
        names=_synchronize(parts,G,matching)
        if names is None:return 'UNKNOWN',None,{'unsynchronized_core':1,'twisted_peels':len(removed)}
    status,c,stats=colour(G,max_nodes=max_nodes)
    stats['twisted_peels']=len(removed)
    if c is None:return status,None,stats
    chosen={v:names[v][k] for v,k in c.items()}
    for u,neighbors in reversed(removed):
        forbidden={matching[v,u][chosen[v]] for v in neighbors}
        chosen[u]=min(set(parts[u])-forbidden)
    active=set(chosen.values())
    word=sum(1<<(x-1) for x,l in signs.items() if (x in active)^(l<0))
    if not all(any(bool(word>>(abs(j)-1)&1)==(j>0) for j in row) for row in clauses) or not all((word&m).bit_count()%2==b for m,b in rows):
        raise AssertionError("source witness failed")
    return status,word,stats
