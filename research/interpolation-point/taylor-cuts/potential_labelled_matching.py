"""Deterministic labelled perfect matching after vertex-potential deletion."""
from itertools import combinations, product
from math import gcd
import networkx as nx


def potentials(n, edges, moduli, deleted):
    """Solve p_u+p_v=g_e off a supplied vertex set; set its own potentials to zero."""
    zero=(0,)*len(moduli)
    adj=[[] for _ in range(n)]
    for u,v,g in edges:
        if u not in deleted and v not in deleted:
            adj[u].append((v,g))
            adj[v].append((u,g))
    result=[zero]*n
    sign={}
    offset={}
    for root in range(n):
        if root in sign or root in deleted:
            continue
        sign[root]=1
        offset[root]=zero
        component=[root]
        doubled=None
        for u in component:
            for v,g in adj[u]:
                child=tuple((a-b)%q for a,b,q in zip(g,offset[u],moduli))
                if v not in sign:
                    sign[v]=-sign[u]
                    offset[v]=child
                    component.append(v)
                elif sign[v]!=sign[u]:
                    if offset[v]!=child:
                        return None
                else:
                    req=tuple((sign[u]*(a-b))%q for a,b,q in zip(child,offset[v],moduli))
                    if doubled is not None and doubled!=req:
                        return None
                    doubled=req
        root_value=[]
        for q,a in zip(moduli,doubled if doubled is not None else zero):
            d=gcd(q,2)
            if a % d:
                return None
            root_value.append((a//d)*pow(2//d,-1,q//d)%(q//d))
        for v in component:
            result[v]=tuple((sign[v]*a+b)%q for a,b,q in zip(root_value,offset[v],moduli))
    return tuple(result)


def search(n, edges, target, *, moduli=None, budget=0, supplied=None, kappa_cap=None):
    """Return (SAT/UNSAT/UNKNOWN, original edge IDs or None, diagnostics)."""
    target=tuple(target)
    moduli=tuple(moduli) if moduli is not None else (3,)*len(target)
    if (type(n) is not int or n<0 or type(budget) is not int or budget<0 or
        len(moduli)!=len(target) or any(type(q) is not int or q<2 for q in moduli)):
        raise ValueError("invalid graph, group or budget")
    def valid(g):
        return len(g)==len(moduli) and all(type(x) is int and 0<=x<q for x,q in zip(g,moduli))
    edges=[(u,v,tuple(g)) for u,v,g in edges]
    if not valid(target) or any(type(u) is not int or type(v) is not int or not 0<=u<n
                               or not 0<=v<n or u==v or not valid(g) for u,v,g in edges):
        raise ValueError("invalid edge or target")
    if kappa_cap is not None and (type(kappa_cap) is not int or kappa_cap<0 or any(q!=3 for q in moduli)):
        raise ValueError("owner-rank mode needs ternary labels and a nonnegative dimension cap")
    if supplied is None:
        choices=(s for k in range(min(n,budget)+1) for s in combinations(range(n),k))
    else:
        supplied=tuple(supplied)
        if len(set(supplied))!=len(supplied) or any(type(v) is not int or not 0<=v<n for v in supplied):
            raise ValueError("invalid supplied modulator")
        choices=[supplied]
    stats=dict(tried_sets=0,matching_calls=0)
    if n%2:
        return "UNSAT",None,stats
    for s in choices:
        stats["tried_sets"]+=1
        cut=set(s)
        p=potentials(n,edges,moduli,cut)
        if p is not None:
            break
    else:
        if kappa_cap is not None:
            return _rank_search(n,edges,target,kappa_cap,None,stats)
        return "UNKNOWN",None,stats
    if kappa_cap is not None:
        return _rank_search(n,edges,target,kappa_cap,(cut,p),stats)
    stats["modulator"]=tuple(sorted(cut))
    zero=(0,)*len(moduli)
    goal=tuple((target[j]-sum(x[j] for x in p))%q for j,q in enumerate(moduli))
    alphabet={v:{zero} for v in cut}
    annotated=[]
    for k,(u,v,g) in enumerate(edges):
        residual=tuple((a-b-c)%q for a,b,c,q in zip(g,p[u],p[v],moduli))
        owner=min((x for x in (u,v) if x in cut),default=None) if residual!=zero else None
        assert residual==zero or owner is not None
        if owner is not None:
            alphabet[owner].add(residual)
        annotated.append((u,v,k,owner,residual))
    order=sorted(cut,key=lambda v:(len(alphabet[v]),v))
    stats["alphabet_sizes"]=tuple(len(alphabet[v]) for v in order)
    if not order and goal!=zero:
        return "UNSAT",None,stats
    for prefix in product(*(sorted(alphabet[v]) for v in order[:-1])):
        contribution=dict(zip(order,prefix))
        if order:
            last=tuple((goal[j]-sum(g[j] for g in prefix))%q for j,q in enumerate(moduli))
            if last not in alphabet[order[-1]]:
                continue
            contribution[order[-1]]=last
        chosen=_ordinary(n,edges,target,moduli,annotated,cut,contribution,stats)
        if chosen is not None:
            return "SAT",chosen,stats
    return "UNSAT",None,stats

def _ordinary(n,edges,target,moduli,annotated,cut,contribution,stats):
    zero=(0,)*len(moduli)
    graph=nx.Graph()
    graph.add_nodes_from(range(n))
    ids={}
    for u,v,k,owner,residual in annotated:
        if any(contribution[x]!=(residual if x==owner else zero) for x in (u,v) if x in cut):
            continue
        pair=tuple(sorted((u,v)))
        if pair not in ids:
            graph.add_edge(*pair)
            ids[pair]=k
    stats["matching_calls"]+=1
    matching=nx.max_weight_matching(graph,maxcardinality=True)
    if 2*len(matching)==n:
        chosen=tuple(sorted(ids[tuple(sorted(e))] for e in matching))
        assert sorted(v for k in chosen for v in edges[k][:2])==list(range(n))
        assert all(sum(edges[k][2][j] for k in chosen)%q==target[j] for j,q in enumerate(moduli))
        return chosen
    return None


def _span_basis(vectors):
    pivots={}
    chosen=[]
    for original in vectors:
        row=original
        for h,v in sorted(pivots.items()):
            if row[h]:
                row=tuple((x-row[h]*y)%3 for x,y in zip(row,v))
        h=next((j for j,x in enumerate(row) if x),None)
        if h is not None:
            pivots[h]=tuple(x*row[h]%3 for x in row)
            chosen.append(original)
    return chosen


def _fiber(columns, goal):
    # RREF the linear map from per-owner affine coordinates to the total label.
    m=len(columns)
    rows=[[col[j] for col in columns]+[rhs] for j,rhs in enumerate(goal)]
    r=0
    pivots=[]
    for i in range(m):
        pivot=next((a for a in range(r,len(rows)) if rows[a][i]),None)
        if pivot is None:
            continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        factor=rows[r][i]
        rows[r]=[factor*x%3 for x in rows[r]]
        for a in range(len(rows)):
            if a!=r and rows[a][i]:
                factor=rows[a][i]
                rows[a]=[(x-factor*y)%3 for x,y in zip(rows[a],rows[r])]
        pivots.append(i)
        r+=1
    if any(row[-1] for row in rows[r:]):
        return None
    free=sorted(set(range(m))-set(pivots))
    return free,pivots,rows[:r]


def _rank_search(n,edges,target,cap,recognized,stats):
    b=len(target)
    zero=(0,)*b
    ambient=set(range(n))
    configurations=[(ambient,[zero]*n)]
    if recognized is not None:
        configurations.insert(0,recognized)
    graph=nx.Graph()
    graph.add_nodes_from(range(n))
    graph.add_edges_from((u,v) for u,v,_ in edges)
    if any(d==0 for _,d in graph.degree):
        return "UNSAT",None,stats
    degree=dict(graph.degree)
    policies=[("id",lambda v:v),("reverse-id",lambda v:-v),
              ("high-degree",lambda v:(-degree[v],v)),("low-degree",lambda v:(degree[v],v))]
    if nx.is_bipartite(graph):
        shore=nx.algorithms.bipartite.color(graph)
        policies.extend([("shore-0",lambda v:(shore[v],v)),("shore-1",lambda v:(-shore[v],v))])
    best=None
    stats["rank_plans"]=0
    for cut,p in configurations:
        goal=tuple((a-sum(pv[j] for pv in p))%3 for j,a in enumerate(target))
        for name,priority in policies:
            annotated=[]
            alph={v:set() for v in cut}
            for k,(u,v,g) in enumerate(edges):
                residual=tuple((x-y-z)%3 for x,y,z in zip(g,p[u],p[v]))
                owner=min((vtx for vtx in (u,v) if vtx in cut),key=priority) if residual!=zero else None
                for vtx in (u,v):
                    if vtx in cut:
                        alph[vtx].add(residual if vtx==owner else zero)
                annotated.append((u,v,k,owner,residual))
            descriptors=[]
            columns=[]
            residual_goal=goal
            for v in sorted(cut):
                origin=min(alph[v])
                basis=_span_basis(tuple((x-y)%3 for x,y in zip(point,origin)) for point in sorted(alph[v]))
                start=len(columns)
                columns.extend(basis)
                descriptors.append((v,origin,start,basis))
                residual_goal=tuple((x-y)%3 for x,y in zip(residual_goal,origin))
            fiber=_fiber(columns,residual_goal)
            stats["rank_plans"]+=1
            if fiber is None:
                stats.update(owner_policy=name,modulator=tuple(sorted(cut)),affine_inconsistent=True)
                return "UNSAT",None,stats
            kappa=len(fiber[0])
            if best is None or kappa<best[0]:
                best=(kappa,tuple(sorted(cut)),name,annotated,alph,descriptors,len(columns),fiber)
    kappa,cut,name,annotated,alph,descriptors,dim,(free,pivots,rows)=best
    stats.update(kappa=kappa,owner_policy=name,modulator=cut,owner_dimensions=dim)
    if kappa>cap:
        return "UNKNOWN",None,stats
    for choice in product(range(3),repeat=kappa):
        point=[0]*dim
        for i,x in zip(free,choice):
            point[i]=x
        for i,row in zip(pivots,rows):
            point[i]=(row[-1]-sum(row[j]*point[j] for j in free))%3
        assignment={}
        for v,origin,pos,basis in descriptors:
            report=tuple((base+sum(point[pos+i]*w[j] for i,w in enumerate(basis)))%3
                         for j,base in enumerate(origin))
            if report not in alph[v]:
                break
            assignment[v]=report
        else:
            chosen=_ordinary(n,edges,target,(3,)*b,annotated,alph,assignment,stats)
            if chosen is not None:
                return "SAT",chosen,stats
    return "UNSAT",None,stats
