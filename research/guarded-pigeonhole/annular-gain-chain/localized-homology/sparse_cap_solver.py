"""Distinguish a candidate from sparse opponents. Labels are zero-based integers."""
from itertools import combinations, product
from graphlib import TopologicalSorter, CycleError


def join(k,h,r,s):
    x=k[h[r]]
    while x!=r:
        if x==s:return True
        x=k[h[x]]
    return False


def solve(candidate, opponents, marks=None):
    """Return (original cap, marks, normalized colors), or None if indistinguishable."""
    n=len(candidate)
    ids=list(range(n))
    if sorted(candidate)!=ids:raise ValueError("invalid candidate")
    inv=[0]*n
    for i,j in enumerate(candidate):inv[j]=i
    adj=[set() for _ in ids]
    triples=[]
    for row in opponents:
        if sorted(row)!=ids:raise ValueError("invalid opponent")
        h=[inv[j] for j in row]
        support=[i for i in ids if h[i]!=i]
        if not support:return None
        if len(support)==2:
            a,b=support
            adj[a].add(b)
            adj[b].add(a)
        elif len(support)==3:
            a=support[0]
            triples.append((a,h[a],h[h[a]]))
        else:raise ValueError("normalized opponent support exceeds three")
    used={x for t in triples for x in t}
    parity={}
    components=[]
    for a in ids:
        if not adj[a] or a in parity:continue
        component=[]
        stack=[a]
        parity[a]=0
        while stack:
            b=stack.pop()
            component.append(b)
            for v in adj[b]:
                if v not in parity:
                    parity[v]=1-parity[b]
                    stack.append(v)
                elif parity[v]==parity[b]:return None
        components.append(component)
    isolated=sorted(used-parity.keys())
    markpairs=[marks] if marks is not None else combinations(ids,2)
    for r,s in markpairs:
        if r not in ids or s not in ids or r==s:raise ValueError("invalid marks")
        fixed={r:0,s:1}
        groups=[]
        for comp in components:
            forced={fixed[x]^parity[x] for x in comp if x in fixed}
            if len(forced)>1:break
            groups.append(sorted(forced) if forced else ((0,1) if used.intersection(comp) else (0,)))
        else:
            for flips in product(*groups):
                base={x:parity[x]^bit for comp,bit in zip(components,flips) for x in comp}
                base.update(fixed)
                for vals in product(*[(fixed[x],) if x in fixed else (-1,0,1) for x in isolated]):
                    colors=dict(base)
                    colors.update(zip(isolated,vals))
                    orders=[TopologicalSorter(),TopologicalSorter()]
                    for x,c in colors.items():
                        if c>=0:
                            root=(r,s)[c]
                            orders[c].add(x,*(() if x==root else (root,)))
                    for triple in triples:
                        cs=[colors[x] for x in triple]
                        if 0 not in cs or 1 not in cs:break
                        if -1 not in cs:
                            i=next(i for i in range(3) if cs.count(cs[i])==1)
                            before,after=triple[(i-1)%3],triple[(i+1)%3]
                            orders[colors[before]].add(after,before)
                    else:
                        try:circle=[x for order in orders for x in order.static_order()]
                        except CycleError:continue
                        cap=ids.copy()
                        for a,b in zip(circle,circle[1:]+circle[:1]):cap[a]=b
                        cap=[cap[inv[j]] for j in ids]
                        return cap,(r,s),[colors.get(x,-1) for x in ids]
    return None


def nae_witness(clauses):
    """Signed integer literals, three per clause. Return (assignment, cap, marks) or None."""
    occurrences={}
    rows=[]
    n=0
    for clause in clauses:
        if len(clause)!=3 or not all(clause):raise ValueError("expected signed triples")
        rows.append((n,n+1,n+2))
        for lit in clause:
            occurrences.setdefault(abs(lit),[]).append((n,lit<0))
            n+=1
    for items in occurrences.values():
        if len(items)==1:
            rows.append((items[0][0],n))
            n+=1
        for (a,x),(b,y) in zip(items,items[1:]):
            if x!=y:rows.append((a,b))
            else:
                rows.extend(((a,n),(n,b)))
                n+=1
    r,s=n,n+1
    ids=list(range(n+2))
    opponents=[]
    for row in rows:
        perm=ids.copy()
        for a,b in zip(row,row[1:]+row[:1]):perm[a]=b
        opponents.append(perm)
    result=solve(ids,opponents,(r,s))
    if result is None:return None
    cap,marks,colors=result
    assignment={v:bool(colors[lst[0][0]])^lst[0][1] for v,lst in occurrences.items()}
    if not all(len({assignment[abs(lit)]^(lit<0) for lit in clause})==2 for clause in clauses):
        raise RuntimeError("invalid decoded assignment")
    return assignment,cap,marks
