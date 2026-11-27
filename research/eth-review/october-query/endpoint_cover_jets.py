"""Ordinary coefficients at physical grid centers for signed OR and COPY rows."""
from itertools import combinations,product
from math import comb
from all_center_packet_jets import JetRing
from variable_packet_machine import shifted_kernel

def evaluate(gates,packets,base,*,center,order,work_cap):
    gates=tuple((k,tuple(p),tuple(s)) for k,p,s in gates)
    packets=tuple(tuple(p) for p in packets)
    if min(order,work_cap)<0 or not packets: raise ValueError('bad parameters')
    L=len(packets[0])
    if L<2 or L&(L-1) or not -L<=center<L or any(len(p)!=L for p in packets):
        raise ValueError('bad layout')
    ports=[p for pack in packets for p in pack if p is not None]
    M=len(ports)
    if M%2 or sorted(ports)!=list(range(M)) or sorted(i for _,ps,_ in gates for i in ps)!=list(range(M)):
        raise ValueError('bad physical ports')
    if any(k not in ('or','copy') or k=='or' and (len(ps)!=len(ss) or any(s not in (0,1) for s in ss))
           for k,ps,ss in gates): raise ValueError('bad gate')
    zero=base.scalar(0)
    if any(k=='or' and not ps for k,ps,_ in gates): return (zero,)*(order+1),dict(empty=True)
    gates=[g for g in gates if g[1]]
    jr=JetRing(base,order+1)
    Z=zero+(base.scalar(1) if order else ())+(0,)*(len(zero)*max(0,order-1))
    ws={d:shifted_kernel(jr,L,center,Z,d) for d in range(1-L,L)}
    modulus=1<<base.p
    c=ws[center][0] if center in ws else 0
    owners={}
    ab={}
    for v,(kind,ps,ss) in enumerate(gates):
        for j,i in enumerate(ps):
            owners[i]=v
            targets=(None,1-ss[j]) if kind=='or' else (0,1)
            ab[i]=tuple((1,0) if t is None else (1-t,2*t-1) for t in targets)
    incid=[[] for _ in range(M//2)]
    corrections=[[] for _ in range(M)]
    for pack in packets:
        for i,row in enumerate(pack):
            if row is None: continue
            successor=i+center
            if 0<=successor<L and pack[successor] is not None: incid[pack[successor]//2].append(row)
            reads={}
            for j,port in enumerate(pack):
                if port is None: continue
                x=port//2
                delta=ws[j-i]
                if j==successor: delta=jr.add(delta,jr.scalar(-c))
                if any(delta[:len(zero)]): raise ArithmeticError('nonzero defect constant')
                reads[x]=jr.add(reads.get(x,jr.scalar(0)),delta)
            corrections[row]=[(x,v) for x,v in reads.items() if any(v)]
    cover=set()
    for ps in incid:
        if len(ps)>2: raise ValueError('bad partial shift')
        own={owners[i] for i in ps}
        if len(own)==2 and own.isdisjoint(cover): cover.add(min(own))
    missing=set(range(M))-{i for ps in incid for i in ps}
    cv=sorted(cover)
    bound=sum(comb(M,k)*L**k for k in range(min(M,order)+1))
    price=bound*(1<<len(cv))*(1+M+len(gates))
    if price>work_cap: return None
    total=jr.scalar(0)
    terms=0
    for k in range(min(M,order)+1):
        for S in combinations(range(M),k):
            marked=set(S)
            for choices in product(*(corrections[i] for i in S)):
                terms+=1
                pin={x for x,d in choices}
                coeff=jr.scalar(1)
                for _,d in choices: coeff=jr.mul(coeff,d)
                scalar=0
                for word in range(1<<len(cv)):
                    fixed={v:word>>i&1 for i,v in enumerate(cv)}
                    unary=[[1,-1 if gate[0]=='or' else 1] for gate in gates]
                    for i in S:
                        for h in (0,1): unary[owners[i]][h]*=ab[i][h][1]
                    for i in missing-marked:
                        for h in (0,1): unary[owners[i]][h]*=ab[i][h][0]
                    const=1
                    for x,ps in enumerate(incid):
                        active=[i for i in ps if i not in marked]
                        unknown={owners[i] for i in active}-cover
                        if len(unknown)>1: raise ArithmeticError('uncovered interaction')
                        v=next(iter(unknown),None)
                        for h in ((0,1) if v is not None else (0,)):
                            off=on=1
                            for i in active:
                                a,b=ab[i][fixed.get(owners[i],h)]
                                off*=a
                                on=on*(a+b*c)%modulus
                            value=on+(0 if x in pin else off)
                            if v is None: const=const*value%modulus
                            else: unary[v][h]=unary[v][h]*value%modulus
                    for v,pair in enumerate(unary):
                        const=const*(pair[fixed[v]] if v in fixed else sum(pair))%modulus
                    scalar=(scalar+const)%modulus
                total=jr.add(total,jr.mul(coeff,jr.scalar(scalar)))
    return tuple(total[i*len(zero):(i+1)*len(zero)] for i in range(order+1)),dict(
        cover=tuple(cv),terms=terms,work_bound=price,precision=base.p,**jr.cost)

def source_rows(n,clauses):
    """Exact port order of source_cnf_driver.count. Return gates,unused,constant.
    constant is None for a nontrivial network or the complete raw count otherwise.
    """
    if n<0: raise ValueError('bad size')
    clean=[]
    for clause in clauses:
        c=set(clause)
        if any(not 1<=abs(x)<=n for x in c): raise ValueError('bad literal')
        if any(-x in c for x in c): continue
        if not c: return (),0,0
        clean.append(tuple(sorted(c,key=abs)))
    if not clean: return (),0,1<<n
    gates=[['or',[],tuple(int(x>0) for x in c)] for c in clean]
    occurs=[[] for _ in range(n)]
    for i,c in enumerate(clean):
        for x in c: occurs[abs(x)-1].append(i)
    edge=0
    def link(a,b):
        nonlocal edge
        gates[a][1].append(2*edge)
        gates[b][1].append(2*edge+1)
        edge+=1
    unused=0
    for batch in occurs:
        d=len(batch)
        if not d:
            unused+=1
            continue
        chain=list(range(len(gates),len(gates)+max(1,d-2)))
        gates.extend(['copy',[],()] for _ in chain)
        for a,b in zip(chain,chain[1:]): link(a,b)
        ends=chain*d if len(chain)==1 else [chain[0],chain[0],*chain[1:-1],chain[-1],chain[-1]]
        for a,b in zip(batch,ends,strict=True): link(a,b)
    return tuple((k,tuple(p),s) for k,p,s in gates),unused,None

def source_jet(n,clauses,packets,ring,*,center,order,work_cap):
    gates,unused,count=source_rows(n,clauses)
    if count is not None: return (ring.scalar(count),)+(ring.scalar(0),)*order,dict(constant=True)
    value=evaluate(gates,packets,ring,center=center,order=order,work_cap=work_cap)
    if value is None: return None
    coeffs,stats=value
    return tuple(ring.mul(c,ring.scalar(1<<unused)) for c in coeffs),dict(stats,unused=unused)
