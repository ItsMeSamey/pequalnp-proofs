"""Learn inconsistent selector partial assignments in one verified data chart."""
from pathlib import Path
from collections import defaultdict
from itertools import combinations,product
from time import perf_counter_ns
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'mixed-ternary-native'))
from solver import chart,block_cover,sub,bits,lift,accepts_cnf,binary_model,parity,_mul,affine_anf


def solve(n,clauses):
    started=perf_counter_ns()
    if type(n) is not int or n<0:raise ValueError('invalid n')
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
    def probe(partial):
        active=full[None].copy()
        for literal in partial:active.extend(full.get(literal,()))
        cost['data_probes']+=1
        return binary_model(d-k,active)
    learned=[]
    for size in range(min(2,k)+1):
        for js in combinations(range(k),size):
            for vals in product((0,1),repeat=size):
                if probe(zip(js,vals)) is None:
                    learned.append(tuple(-(j+1) if v else j+1 for j,v in zip(js,vals)))
    cost['learned_rows']=len(learned)
    word=binary_model(k,learned)
    if word is None:return finish('unsat','selector 2SAT')
    data=probe((j,(word>>j)&1) for j in range(k))
    if data is None:return finish('skip','full activation exceeds pair explanations')
    return finish('sat','full fiber',lift(physical,lift(old,word|(data<<k))))
