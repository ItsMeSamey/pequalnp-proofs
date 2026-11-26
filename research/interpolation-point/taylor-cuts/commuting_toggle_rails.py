"""Count closed permutation rails by a shared control precedence order."""
from itertools import product
from graphlib import TopologicalSorter


def compose(p,q):
    return tuple(p[x] for x in q)


def inverse(p):
    out = [0]*len(p)
    for i,x in enumerate(p):
        out[x] = i
    return tuple(out)


def decode_table(size,rows):
    """Validate a grouped relation (control value,input state,output state)."""
    if not isinstance(size,int) or size<1:
        raise ValueError("invalid state-domain size")
    targets=[[set() for _ in range(size)] for _ in range(2)]
    for bit,i,j in rows:
        if bit not in (0,1) or any(not isinstance(x,int) or not 0<=x<size for x in (i,j)):
            raise ValueError("invalid transition row")
        targets[bit][i].add(j)
    if any(len(cell)!=1 for side in targets for cell in side):
        raise ValueError("table is not a total function")
    perms=tuple(tuple(next(iter(cell)) for cell in side) for side in targets)
    if any(len(set(p))!=size for p in perms):
        raise ValueError("table is not bijective")
    return perms


def precedence_blocks(words):
    """Topological order of SCCs from noncommuting forward occurrence pairs."""
    nodes={abs(lit) for word in words for lit,_ in word}
    graph={v:set() for v in nodes}
    for word in words:
        for i,(lit,p) in enumerate(word):
            for other,q in word[i+1:]:
                if abs(lit)!=abs(other) and compose(p,q)!=compose(q,p):
                    graph[abs(lit)].add(abs(other))
    # Iterative Kosaraju keeps the recognizer independent of recursion limits.
    reverse={v:set() for v in nodes}
    for u in nodes:
        for v in graph[u]:
            reverse[v].add(u)
    seen=set()
    order=[]
    for start in sorted(nodes):
        if start in seen:
            continue
        seen.add(start)
        stack=[(start,iter(graph[start]))]
        while stack:
            u,it=stack[-1]
            v=next(it,None)
            if v is None:
                order.append(u)
                stack.pop()
            elif v not in seen:
                seen.add(v)
                stack.append((v,iter(graph[v])))
    owner={}
    for start in reversed(order):
        if start in owner:
            continue
        stack=[start]
        owner[start]=start
        while stack:
            for v in reverse[stack.pop()]:
                if v not in owner:
                    owner[v]=start
                    stack.append(v)
    dag=TopologicalSorter()
    for u in nodes:
        dag.add(owner[u])
        for v in graph[u]:
            if owner[v]!=owner[u]:
                dag.add(owner[v],owner[u])
    return [tuple(sorted(v for v in nodes if owner[v]==r)) for r in dag.static_order()]


def count_rails(n,rails):
    """Return (count, original witness); a rail is (size, signed gates).

    A gate is (signed one-based control ID, P0, P1). Witness paths include
    the starting state and its closing copy; an empty rail has one state port.
    """
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid control count")
    specs,baselines,words,sizes=[],[],[],[]
    for size,gates in rails:
        if not isinstance(size,int) or size<1:
            raise ValueError("invalid domain size")
        identity=tuple(range(size))
        frame=identity
        word=[]
        gates=tuple((lit,tuple(p),tuple(q)) for lit,p,q in gates)
        for lit,p,q in gates:
            if not isinstance(lit,int) or not 1<=abs(lit)<=n:
                raise ValueError("invalid signed control")
            if any(len(a)!=size or set(a)!=set(identity) for a in (p,q)):
                raise ValueError("transition must be a permutation")
            newframe=compose(p,frame)
            word.append((lit,compose(inverse(newframe),compose(q,frame))))
            frame=newframe
        specs.append(gates)
        sizes.append(size)
        baselines.append(frame)
        words.append(word)
    blocks=precedence_blocks(words)
    tables=[]
    for block in blocks:
        rows=[]
        positions={v:i for i,v in enumerate(block)}
        local=[[(positions[abs(lit)],lit<0,p) for lit,p in word if abs(lit) in positions]
               for word in words]
        for bits in range(1<<len(block)):
            mask=sum(1<<(v-1) for v,i in positions.items() if bits>>i&1)
            perms=[]
            for size,occurrences in zip(sizes,local):
                perm=tuple(range(size))
                for i,negative,p in occurrences:
                    if (bits>>i&1)^negative:
                        perm=compose(p,perm)
                perms.append(perm)
            rows.append((mask,perms))
        tables.append(rows)
    unused=n-sum(map(len,blocks))
    count,witness=0,None
    for start in product(*(range(size) for size in sizes)):
        states={start:(1,0)}
        for table in tables:
            nxt={}
            for state,(ways,mask) in states.items():
                for selected,perms in table:
                    target=tuple(p[x] for p,x in zip(perms,state))
                    prior=nxt.get(target)
                    nxt[target]=(prior[0]+ways,prior[1]) if prior else (ways,mask|selected)
            states=nxt
        for end,(ways,mask) in states.items():
            if any(b[x]!=s for b,x,s in zip(baselines,end,start)):
                continue
            count+=ways << unused
            if witness is None:
                paths=[]
                for s,gates in zip(start,specs):
                    path=[s]
                    for lit,p,q in gates:
                        bit=((mask>>(abs(lit)-1))&1) ^ (lit<0)
                        path.append((p,q)[bit][path[-1]])
                    assert path[-1]==s
                    paths.append(tuple(path))
                witness=mask,tuple(paths)
    return count,witness
