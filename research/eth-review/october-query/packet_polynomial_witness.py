"""Exact integer D^M F(T) of signed-OR/COPY source rows on one common packet layout."""
from itertools import product
from math import prod,comb
from fractions import Fraction
from endpoint_cover_jets import source_rows

def mul(a,b):
    if not a or not b: return []
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): c[i+j]+=x*y
    while c and not c[-1]: c.pop()
    return c

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=x
    while c and not c[-1]: c.pop()
    return c

def evaluate(gates,packets,*,work_cap,unused=0,packet_order=None,pins=()):
    """Supplied layout checks coverage/packet width; source labeling admission is separate."""
    gates=tuple((k,tuple(ps),tuple(ss)) for k,ps,ss in gates)
    pk=tuple(tuple(p) for p in packets)
    if work_cap<0 or unused<0 or not pk: raise ValueError('invalid cap or packet list')
    L=len(pk[0])
    if L<2 or L&(L-1) or any(len(p)!=L for p in pk): raise ValueError('bad width')
    real=[i for p in pk for i in p if i is not None]
    M=len(real)
    if M%2 or sorted(real)!=list(range(M)) or sorted(i for _,ps,_ in gates for i in ps)!=list(range(M)):
        raise ValueError('invalid port coverage')
    own={}
    for j,(kind,ps,ss) in enumerate(gates):
        if kind not in ('or','copy') or not ps or (kind=='or' and (len(ss)!=len(ps) or any(s not in (0,1) for s in ss))):
            raise ValueError('invalid nonempty source gate')
        for t,i in enumerate(ps): own[i]=(j,ss[t] if kind=='or' else None)
    pins=dict(pins)
    if any(not 0<=e<M//2 or b not in (0,1) for e,b in pins.items()): raise ValueError('invalid physical pin')
    if packet_order is not None:
        route=tuple(packet_order)
        if len(set(route))!=len(route) or any(type(i) is not int or not 0<=i<len(pk) for i in route):
            raise ValueError('invalid supplied order')
        missing=set(range(len(pk)))-set(route)
        if any(any(x is not None for x in pk[i]) for i in missing): raise ValueError('missing real packet')
        route+=tuple(sorted(missing))
    G=len(gates)
    scopes=[{j for i in p if i is not None for j in (own[i][0],G+i//2)} for p in pk]
    pending=set(range(len(pk)))
    seen=set()
    remaining={j:sum(j in s for s in scopes) for s in scopes for j in s}
    order=[]
    estimate=0
    peak=0
    D=prod(-q for q in range(-L,L) if q)
    # Costs count scalar integer multiplications/additions with polynomial degrees
    # bounded by M(2L-1); coefficient bit lengths also depend on L and raw data.
    N=M*(2*L-1)+1
    estimate+=(2*L-1)*(2*L)**2*4*L
    while pending:
        def measure(j):
            extended=seen|scopes[j]
            after={v for v in extended if remaining[v]>int(v in scopes[j])}
            return len(extended),len(after),j
        j=min(pending,key=measure) if packet_order is None else route[len(order)]
        ext=sorted(seen|scopes[j])
        after=sorted(v for v in ext if remaining[v]>int(v in scopes[j]))
        first=scopes[j]-seen
        price=(1<<len(ext))*(1+M+L)**2*N*N*4
        estimate+=price
        if estimate>work_cap: return dict(status='unknown',reason='work_cap',required_at_least=estimate)
        order.append((j,tuple(sorted(seen)),ext,after,first))
        peak=max(peak,len(ext))
        for v in scopes[j]: remaining[v]-=1
        seen=set(after)
        pending.remove(j)
    kernels={}
    for d in range(1-L,L):
        pol=[1]
        for q in range(-L,L):
            if d!=q: pol=mul(pol,[-q,1])
        kernels[d]=pol
    table={0:[1]}
    for j,before,ext,after,first in order:
        p=pk[j]
        idx={v:i for i,v in enumerate(ext)}
        nxt={}
        for w in range(1<<len(ext)):
            def bit(v): return w>>idx[v]&1
            if any(not bit(G+e)==pins[e] for e in pins if G+e in first): continue
            def state(vs): return sum(bit(v)<<i for i,v in enumerate(vs))
            acc=table.get(state(before))
            if not acc: continue
            factor=[(-1)**sum(bit(v) for v in first if v<G and gates[v][0]=='or')]
            for x,row in enumerate(p):
                if row is None: continue
                v,s=own[row]
                h=bit(v)
                target=h if s is None else 1-s if h else None
                if target is None: f=[D]
                else:
                    read=[]
                    for y,col in enumerate(p):
                        if col is not None and bit(G+col//2): read=add(read,kernels[y-x])
                    f=read if target else add([D],[-z for z in read])
                factor=mul(factor,f)
                if not factor: break
            if factor:
                key=state(after)
                nxt[key]=add(nxt.get(key,[]),mul(acc,factor))
        table=nxt
    numerator=tuple(x<<unused for x in table.get(0,[])) or (0,)
    denominator=D**M
    count,rem=divmod(numerator[0],denominator)
    if rem: raise ArithmeticError('origin not integral')
    return dict(status='exact',numerator=numerator,denominator=denominator,count=count,
                packet_order=tuple(j for j,*_ in order),max_enum_width=peak,work_bound=estimate)

def source(n,clauses,packets,*,work_cap,fallback=None):
    raw=tuple(tuple(c) for c in clauses)
    gates,unused,constant=source_rows(n,raw)
    if constant is not None: return dict(status='exact',count=constant,numerator=(constant,),denominator=1)
    result=evaluate(gates,packets,work_cap=work_cap,unused=unused)
    if result['status']=='unknown' and fallback is not None: return fallback(n,raw,packets)
    return result

def jets(result,t,alpha,order):
    if result['status']!='exact' or order<0: raise ValueError('need exact polynomial')
    p=result['numerator']
    return tuple(Fraction(sum(p[k]*comb(k,j)*t**(k-j) for k in range(j,len(p)))*alpha**j,
                          result['denominator']) for j in range(order+1))

def half_source(n,clauses,*,work_cap,layout_options):
    """Construct a full half-separated template; strict admission is recorded explicitly."""
    from half_separated_packets import from_clauses
    raw=tuple(tuple(c) for c in clauses)
    layout=from_clauses(n,raw,**layout_options)
    if layout['status']=='constant':
        c=layout['raw_count']
        return dict(status='exact',count=c,numerator=(c,),denominator=1)
    if layout['status']!='exact': return layout
    result=source(n,raw,layout['plan'][2],work_cap=work_cap)
    return dict(result,strict_template=layout['strict'],native_schedule_executed=False,
                padded_slots=layout['padded_slots'])

def solve(n,clauses,packets,*,work_cap,packet_order=None,witness=True):
    """Same-layout count and checked raw witness. work_cap is cumulative across all passes."""
    raw=tuple(tuple(c) for c in clauses)
    if n<0 or work_cap<0 or any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('bad input')
    packets=tuple(tuple(pk) for pk in packets)
    gates,unused,constant=source_rows(n,raw)
    if constant is not None:
        return dict(status='exact',count=constant,numerator=(constant,),denominator=1,
                    witness=0 if constant and witness else None,passes=0,total_work=0)
    clean=[]
    for c in raw:
        values=set(c)
        if not any(-x in values for x in values): clean.append(tuple(sorted(values,key=abs)))
    representatives={}
    for c,(kind,ports,signs) in zip(clean,gates):
        for lit,e in zip(c,ports,strict=True): representatives.setdefault(abs(lit),e//2)
    order=None if packet_order is None else tuple(packet_order)
    ans=evaluate(gates,packets,work_cap=work_cap,unused=unused,packet_order=order)
    if ans['status']!='exact': return ans
    total=ans['work_bound']
    passes=1
    if not witness or not ans['count']: return dict(ans,witness=None,passes=passes,total_work=total)
    w=0
    pins={}
    # Materialized route is also reused when the first call discovered it automatically.
    for x,e in sorted(representatives.items()):
        pins[e]=0
        test=evaluate(gates,packets,work_cap=work_cap-total,unused=unused,packet_order=ans['packet_order'],pins=pins)
        if test['status']!='exact':
            return dict(status='unknown',reason='witness_budget',exact_count=ans['count'],passes=passes,total_work=total)
        total+=test['work_bound']
        passes+=1
        if test['count']==0:
            pins[e]=1
            w|=1<<(x-1)
    if not all(any(bool((w>>(abs(x)-1))&1)==(x>0) for x in c) for c in raw):
        raise ArithmeticError('invalid original witness')
    return dict(ans,witness=w,passes=passes,total_work=total)
