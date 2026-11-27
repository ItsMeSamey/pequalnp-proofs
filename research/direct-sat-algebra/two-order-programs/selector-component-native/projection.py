"""Project compiled guarded binary data components onto incident selectors."""
from pathlib import Path
from collections import defaultdict
from itertools import combinations,product
from time import perf_counter_ns
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'mixed-ternary-native'))
from solver import chart,block_cover,sub,bits,lift,accepts_cnf,binary_model,parity,_mul,affine_anf


from route import solve as solve_tables


def solve(n,clauses,*,scope_cap=4,table_cap=65536,fallback_limit=0):
    started=perf_counter_ns()
    if type(n) is not int or n<0:raise ValueError('invalid n')
    if any(type(v) is not int or v<0 for v in (scope_cap,table_cap,fallback_limit)):raise ValueError("invalid resource caps")
    raw=tuple(tuple(row) for row in clauses)
    if any(type(l) is not int or not 1<=abs(l)<=n for row in raw for l in row):raise ValueError('invalid literal')
    cost=dict(n=n,clauses=len(raw),cells=0,data_probes=0)
    def finish(status,reason,w=None):
        if status=='sat' and not accepts_cnf(raw,w):raise AssertionError('original witness mismatch')
        cost['elapsed_ns']=perf_counter_ns()-started
        return dict(status=status,reason=reason,witness=w,cost=cost)
    tables=defaultdict(dict)
    for row in raw:
        c=set(row)
        if any(-l in c for l in c):continue
        if len(c)>3:return finish('skip','width')
        sites=tuple(sorted(abs(l)-1 for l in c))
        tables[sites][sum((-(s+1) in c)<<j for j,s in enumerate(sites))]=tuple(sorted(c))
    eq=[];res=[]
    for sites,patterns in tables.items():
        size=1<<len(sites);cost['cells']+=size
        valid=[x for x in range(size) if x not in patterns]
        if not valid:return finish('unsat','empty group')
        if len(sites)==3:
            normals=[v for v in range(1,size) if all(not parity(v&(x^valid[0])) for x in valid)]
            eq.extend((sum(1<<sites[j] for j in bits(v)),parity(v&valid[0])) for v in normals)
            if len(valid)*(1+len(normals))==size:continue
        res.extend(patterns.values())
    mapped=chart(n,eq)
    if mapped is None:return finish('unsat','affine contradiction')
    d,physical=mapped
    rows=[tuple(physical[abs(l)-1]^int(l>0) for l in row) for row in res]
    sels=block_cover([tuple(f>>1 for f in row) for row in rows],d)
    if sels is None:return finish('skip','no block cover')
    k=len(sels);cost['selectors']=k
    basis={}
    def reduce(v):
        c=0
        while v:
            p=v.bit_length()-1
            if p not in basis:break
            w,carry=basis[p];v^=w;c^=carry
        return v,c
    def insert(v):
        rem,c=reduce(v)
        if rem:basis[rem.bit_length()-1]=(rem,c^(1<<len(basis)))
    for v in sels:insert(v)
    for row in sorted(rows,key=lambda row:len(row)>2):
        for f in row:insert(f>>1)
    for i in range(d):insert(1<<i)
    old=[reduce(1<<i)[1]<<1 for i in range(d)]
    full=defaultdict(list)
    for row in rows:
        poly={0}
        for f in row:poly=_mul(poly,affine_anf(sub(f,old)))
        support=0
        for t in poly:support |= t
        gu=tuple(bits(support&((1<<k)-1)))
        data=tuple(bits(support>>k))
        if len(gu)>int(len(row)==3) or len(data)>2:return finish('skip','unsupported common chart')
        for sv in range(1<<len(gu)):
            guard=(gu[0],sv) if gu else None
            for vals in product((0,1),repeat=len(data)):
                x=sum(v<<(k+j) for v,j in zip(vals,data))|(sv<<gu[0] if gu else 0)
                if sum((x&t)==t for t in poly)&1:
                    full[guard].append(tuple(-(j+1) if v else j+1 for j,v in zip(data,vals)))
    cost['data_bits']=d-k;cost['compiled_binary_rows']=sum(map(len,full.values()))
    data_n=d-k
    parent=list(range(data_n))
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]];i=parent[i]
        return i
    for records in full.values():
        for row in records:
            if len(row)==2:parent[root(abs(row[0])-1)]=root(abs(row[1])-1)
    buckets=defaultdict(list)
    direct=defaultdict(list)
    for guard,records in full.items():
        for row in records:
            if row:buckets[root(abs(row[0])-1)].append((guard,row))
            elif guard is None:return finish('unsat','unconditional empty data clause')
            else:direct[(guard[0],)].append(guard[1])
    groups={}
    for scope,forbidden in direct.items():
        groups[scope]=set(range(2))-set(forbidden)
    compiled=[]
    cost.update(component_widths=[],table_probes=0,traceback_probes=0,
                fallback_evaluations=0,components=len(buckets),projected_table_cells=0)
    for records in buckets.values():
        scope=tuple(sorted({guard[0] for guard,_ in records if guard is not None}))
        cost['component_widths'].append(len(scope))
        if len(scope)>scope_cap:return finish('skip','component width cap')
        size=1<<len(scope)
        if cost['projected_table_cells']+size>table_cap:return finish('skip','table cap')
        cost['projected_table_cells']+=size
        ids=sorted({abs(l)-1 for _,row in records for l in row})
        idx={v:i+1 for i,v in enumerate(ids)}
        scope_idx={v:i for i,v in enumerate(scope)}
        local_rows=[(None if g is None else (scope_idx[g[0]],g[1]),
                     tuple(idx[abs(l)-1]*(1 if l>0 else -1) for l in row)) for g,row in records]
        compiled.append((scope,ids,local_rows))
        accepted=set()
        for word in range(size):
            active=[r for g,r in local_rows if g is None or (word>>g[0])&1==g[1]]
            cost['table_probes']+=1
            if binary_model(len(ids),active) is not None:accepted.add(word)
        if scope in groups:groups[scope]&=accepted
        else:groups[scope]=accepted
    cost['merged_scopes']=len(groups)
    denied=[];unary=[];is_product=True
    for scope,valid in groups.items():
        if not valid:return finish('unsat','empty projected intersection')
        size=1<<len(scope)
        rectangle=1
        for j,v in enumerate(scope):
            vals={(w>>j)&1 for w in valid}
            rectangle*=len(vals)
            if len(vals)==1:unary.append((v,next(iter(vals))))
        is_product &= rectangle==len(valid)
        for word in set(range(size))-valid:
            denied.append(tuple(-(v+1) if (word>>j)&1 else v+1 for j,v in enumerate(scope)))
    cost['projected_forbidden_rows']=len(denied)
    if is_product:
        pins={}
        for j,v in unary:
            if j in pins and pins[j]!=v:return finish('unsat','projected units conflict')
            pins[j]=v
        selector=sum(v<<j for j,v in pins.items())
        cost['join']='unary';cost['selector_units']=len(pins)
    else:
        joined=solve_tables(k,denied,arity=max(1,scope_cap),
                            max_cells=sum(1<<len(s) for s in groups))
        cost.update(join=joined.route,join_table_cells=joined.cells,join_generated=joined.generated)
        if joined.status=='UNSAT':return finish('unsat','projected '+joined.route)
        selector=joined.witness
        if joined.status=='SKIP':
            cost['initial_join']=cost['join']
            cost['join']='bounded selector enumeration'
            for candidate in range(min(1<<k,fallback_limit)):
                cost['fallback_evaluations']+=1
                if accepts_cnf(denied,candidate):
                    selector=candidate;break
            if selector is None:
                if cost['fallback_evaluations']==1<<k:return finish('unsat','exhaustive selector join')
                return finish('skip','unrecognized projected join')
    data=0
    for scope,ids,local_rows in compiled:
        word=sum(((selector>>v)&1)<<i for i,v in enumerate(scope))
        active=[r for g,r in local_rows if g is None or (word>>g[0])&1==g[1]]
        x=binary_model(len(ids),active);cost['traceback_probes']+=1
        if x is None:raise AssertionError('projected component failed traceback')
        data|=sum(((x>>i)&1)<<v for i,v in enumerate(ids))
    cost['selector_word']=selector
    return finish('sat','projected '+cost['join'],lift(physical,lift(old,selector|(data<<k))))
