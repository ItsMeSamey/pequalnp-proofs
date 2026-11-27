"""Exact counted compiler portfolio with deterministic exhaustive original-CNF fallback."""
from affine_mst_cnf import Compilation,add,plug
from signed_cover_projection import normalized,sat

def compile(n,clauses,*,scope_cap,table_cap,observable_ids=None):
    if min(n,scope_cap,table_cap)<0: raise ValueError('invalid bound')
    raw=tuple(tuple(c) for c in clauses)
    if any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('bad literal')
    rows=normalized(raw)
    unsat=Compilation(n,raw,((),),(),(),(),0)
    if frozenset() in rows: return unsat
    groups={}
    for c in rows:
        mask=sum(1<<(abs(x)-1) for x in c)
        p=sum(x<0 for x in c)%2
        groups.setdefault((mask,p),[]).append(c)
    piv={}
    equations=[]
    for (mask,p),block in groups.items():
        if len(block)==1<<(mask.bit_count()-1):
            eq=mask,1^p
            if not add(*eq,piv): return unsat
            equations.append(eq)
            rows.difference_update(block)
    clauses=[]
    directions={}
    for c in sorted(rows,key=lambda a:(len(a),sorted(a))):
        reduced={plug(1<<(abs(x)-1),int(x<0),piv) for x in c}
        false_system={}
        if not all(add(a,b,false_system) for a,b in reduced): continue
        reduced.discard((0,0))
        if not reduced: return unsat
        clauses.append(sorted(reduced))
        for a,b in reduced: add(a,0,directions)
    basis=[]
    rep={}
    offsets=0
    def express(a):
        e=0
        for j in sorted(rep,reverse=True):
            if a>>j&1:
                v,f=rep[j]
                a^=v
                e^=f
        return a,e
    if observable_ids is not None:
        ids=tuple(observable_ids)
        if len(ids)!=len(directions) or any(not 1<=i<=n for i in ids): return None
        for i in ids:
            rawmask=1<<(i-1)
            a,b=plug(rawmask,0,piv)
            if plug(a,0,directions)[0]: return None
            v,e=express(a)
            if not v: return None
            j=len(basis)
            rep[v.bit_length()-1]=(v,e^(1<<j))
            offsets|=b<<j
            basis.append(rawmask)
    residual=[]
    for c in clauses:
        forms=[]
        for a,b in c:
            v,e=express(a)
            if v:
                if observable_ids is not None: raise ArithmeticError('incorrect span')
                j=len(basis)
                basis.append(v)
                rep[v.bit_length()-1]=(v,1<<j)
                e^=1<<j
            forms.append((e,b^((e&offsets).bit_count()%2)))
        residual.append(tuple(sorted(forms)))
    r=len(basis)
    sig=[[sum(((a>>i)&1)<<j for j,(a,b) in enumerate(c)) for c in residual] for i in range(r)]
    sig=[[0]*len(residual)]+sig
    edges=sorted((sum(a!=b for a,b in zip(sig[i],sig[j])),i,j) for i in range(r+1) for j in range(i))
    parent=list(range(r+1))
    def find(i):
        while i!=parent[i]:
            parent[i]=parent[parent[i]]
            i=parent[i]
        return i
    tree=[]
    for _,i,j in edges:
        a,b=find(i),find(j)
        if a!=b:
            parent[a]=b
            tree.append((i,j))
    out=set()
    cost=0
    for ci,c in enumerate(residual):
        active=[j for j,(u,v) in enumerate(tree) if sig[u][ci]!=sig[v][ci]]
        if len(active)>scope_cap or (1<<len(active))>table_cap-cost: return None
        cost+=1<<len(active)
        forms=[]
        for k,(_,b) in enumerate(c):
            a=sum((((sig[tree[j][0]][ci]^sig[tree[j][1]][ci])>>k)&1)<<t for t,j in enumerate(active))
            forms.append((a,b))
        for w in range(1<<len(active)):
            if any(((a&w).bit_count()%2)^b for a,b in forms): continue
            out.add(tuple(-(j+1) if w>>t&1 else j+1 for t,j in enumerate(active)))
    return Compilation(n,raw,tuple(sorted(out)),tuple(tree),tuple(basis),tuple(equations),1<<(n-len(piv)-r))

def enumerate_count(n,clauses):
    """Reference exact backend, exponential in the declared variable count."""
    count=0
    witness=None
    for w in range(1<<n):
        if all(sat(c,w) for c in clauses):
            count+=1
            if witness is None: witness=w
    return count,witness

def solve(n,clauses,*,scope_cap,table_cap,chart_word_cap,observable_ids=None,original_backend=None):
    """Original backend contract: exact (count, raw witness or None) on (n,raw).
    Its full runtime is charged to the caller. Each attempted chart has its own caps.
    """
    if chart_word_cap<0: raise ValueError('negative chart cap')
    raw=tuple(tuple(c) for c in clauses)
    charts=[('automatic',None)]
    if observable_ids is not None: charts.insert(0,('supplied',tuple(observable_ids)))
    attempts=[]
    for name,ids in charts:
        chart=compile(n,raw,scope_cap=scope_cap,table_cap=table_cap,observable_ids=ids)
        if chart is None:
            attempts.append((name,'invalid-or-expansion-cap'))
            continue
        if chart.fiber==0: return dict(count=0,witness=None,route=name,attempts=attempts+[(name,'contradiction')])
        if 1<<len(chart.tree)>chart_word_cap:
            attempts.append((name,'chart-word-cap'))
            continue
        count,w=enumerate_count(len(chart.tree),chart.clauses)
        return dict(count=count*chart.fiber,witness=None if w is None else chart.lift(w),
                    route=name,attempts=attempts+[(name,'accepted')])
    count,w=(original_backend or enumerate_count)(n,raw)
    if not isinstance(count,int) or not 0<=count<=1<<n or (count==0)!=(w is None):
        raise ValueError('invalid original backend answer')
    if w is not None and (not isinstance(w,int) or not 0<=w<1<<n or not all(sat(c,w) for c in raw)):
        raise ValueError('invalid original witness')
    return dict(count=count,witness=w,route='original-backend' if original_backend is not None else 'original-exhaustive',
                attempts=attempts)
