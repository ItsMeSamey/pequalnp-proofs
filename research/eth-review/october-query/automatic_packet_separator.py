"""Bounded deterministic half-separated layout search on original signed-CNF ports."""
from collections import defaultdict
from math import factorial
from half_separated_packets import from_clauses
from packet_layout import SourcePlan, rounded_power
from source_grid_cnf_band import _compile


def _scope_profile(order, scopes, m, L, packet_count):
    union=0
    suffix=[0]*(len(order)+1)
    for i in range(len(order)-1,-1,-1):
        suffix[i]=suffix[i+1]|scopes[order[i]]
    peak=0
    visits=packet_count-len(order)  # executor appends the all-dummy factors
    stored=2
    for i,j in enumerate(order):
        before=union & suffix[i]
        joint=before|scopes[j]
        union|=scopes[j]
        after=union & suffix[i+1]
        peak=max(peak,joint.bit_count())
        stored=max(stored,(1<<before.bit_count())+(1<<after.bit_count()))
        visits+=1<<joint.bit_count()
    degree=m*(2*L-1)
    return dict(width=peak,word_visits=visits,peak_table_entries=stored,
                executor_price=(2*L-1)*(2*L)**2*4*L+visits*4*(1+m+L)**2*(degree+1)**2,
                coefficient_slots=stored*(degree+1),degree=degree)


def _order(scopes, active, exact, stats):
    count=len(active)
    if exact:
        # Minimum possible maximum joint width over all sequential orders.
        full=(1<<count)-1
        unions=[0]*(full+1)
        best=[0]*(full+1)
        prev=[None]*(full+1)
        for mask in range(1,full+1):
            bit=mask&-mask
            unions[mask]=unions[mask^bit]|scopes[active[bit.bit_length()-1]]
        for mask in range(1,full+1):
            rest=mask
            while rest:
                bit=rest&-rest
                rest^=bit
                j=active[bit.bit_length()-1]
                old=mask^bit
                live=unions[old]&unions[full^old]
                w=max(best[old],(live|scopes[j]).bit_count())
                stats['order_transitions']+=1
                if prev[mask] is None or w<best[mask]:
                    best[mask],prev[mask]=w,bit
        reverse=[]
        while full:
            bit=prev[full]
            reverse.append(active[bit.bit_length()-1])
            full^=bit
        return tuple(reversed(reverse))
    pending=set(active)
    order=[]
    seen=0
    counts=defaultdict(int)
    for i in active:
        for bit in _bits(scopes[i]):
            counts[bit]+=1
    while pending:
        def price(i):
            joint=seen|scopes[i]
            dying=sum(1 for b in _bits(scopes[i]) if counts[b]==1)
            return joint.bit_count(),joint.bit_count()-dying,i
        i=min(pending,key=price)
        stats['order_transitions']+=len(pending)
        pending.remove(i)
        order.append(i)
        seen|=scopes[i]
        for bit in _bits(scopes[i]):
            counts[bit]-=1
            if counts[bit]==0:
                seen^=bit
    return tuple(order)


def _bits(mask):
    while mask:
        b=mask&-mask
        yield b
        mask^=b


def _unrank(values,rank,ways):
    # None denotes indistinguishable dummies; actual absolute ports are unique.
    counts=defaultdict(int)
    for v in values:
        counts[-1 if v is None else v]+=1
    out=[]
    for size in range(len(values),0,-1):
        for k in sorted(counts):
            block=ways*counts[k]//size
            if rank<block:
                out.append(None if k==-1 else k)
                ways=block
                counts[k]-=1
                if not counts[k]:
                    del counts[k]
                break
            rank-=block
    return out


def recognize(n,clauses,*,r,a,u,delta,slot_cap,placement_cap,width_cap,
              order_state_cap=0,strict=True,pins=()):
    """Search a fixed legal label/orientation/half template; cap counts actual layouts tested.

    pins are fixed (physical COPY2-bit index,value) pairs, retained for readout;
    the dense joint-width bound stays valid even for the unpinned polynomial.
    """
    if min(placement_cap,width_cap,order_state_cap,slot_cap)<0:
        raise ValueError('negative search cap')
    raw=tuple(tuple(row) for row in clauses)
    pins=tuple(pins)
    seed=from_clauses(n,raw,r=r,a=a,u=u,delta=delta,slot_cap=slot_cap,strict=strict)
    if seed['status']!='exact':
        if seed['status']=='constant' and pins: raise ValueError('no physical root to pin')
        if seed['status']=='unknown': return dict(seed,requested_pins=pins)
        return seed
    gates=seed['gates']
    a,u,pk,shells=seed['plan']
    m=sum(len(ps) for _,ps,_ in gates)
    fixed={}
    for x,b in pins:
        if type(x) is not int or not 0<=x<m//2 or b not in (0,1) or x in fixed and fixed[x]!=b:
            raise ValueError('invalid or conflicting physical pin')
        fixed[x]=int(b)
    L=1<<a
    port_scope=[0]*m
    for i,(_,ps,_) in enumerate(gates):
        for x in ps:
            port_scope[x]=(1<<i)|(1<<(len(gates)+x//2))
    buckets=defaultdict(list)
    flat=[x for packet in pk for x in packet]
    for k,(pat,flip) in enumerate(seed['metadata']):
        mask=sum(1<<i for i,(x,y) in enumerate(pat) if x!=y)
        for j in range(L):
            key=(pat,(j^flip)&mask,int(j>=L//2))
            buckets[key].append(k*L+j)
    free=[]; total=1
    for slots in buckets.values():
        values=[flat[i] for i in slots]
        if not any(v is not None for v in values):
            continue
        ways=factorial(len(slots))//factorial(values.count(None))
        if ways>1:
            free.append((slots,values,ways))
            total*=ways
    stats=dict(template_slots=len(flat),placements=0,possible_placements=total,
               order_transitions=0,largest_exact_order_states=0,ranked_layouts_inspected=0,
               layout_build_port_square_bound=m*m,all_orders_exact=True)
    best=None
    def test(candidate):
        nonlocal best
        stats['placements']+=1
        packets=tuple(tuple(candidate[i:i+L]) for i in range(0,len(candidate),L))
        scopes=[]
        for packet in packets:
            scope=0
            for x in packet:
                if x is not None:
                    scope|=port_scope[x]
            scopes.append(scope)
        active=tuple(i for i,s in enumerate(scopes) if s)
        exact=len(active)<order_state_cap.bit_length() and (1<<len(active))<=order_state_cap
        stats['all_orders_exact'] &= exact
        if exact:
            stats['largest_exact_order_states']=max(stats['largest_exact_order_states'],1<<len(active))
        order=_order(scopes,active,exact,stats)
        profile=_scope_profile(order,scopes,m,L,len(packets))
        if best is None or profile['width']<best:
            best=profile['width']
        if profile['width']<=width_cap:
            return dict(status='found',plan=(a,u,packets,shells),labels=seed['labels'],
                        metadata=seed['metadata'],H_pad=seed['H_pad'],strict=strict,
                        packets=packets,packet_order=order,pins=tuple(sorted(fixed.items())),
                        unused_raw_bits=seed['unused_raw_bits'],profile=profile,stats=stats)
        return None
    if placement_cap:
        ans=test(flat)
        if ans is not None: return ans
    for rank in range(total):
        if stats['placements']>=min(total,placement_cap): break
        candidate=flat.copy()
        q=rank
        stats['ranked_layouts_inspected']+=1
        for slots,values,ways in free:
            q,k=divmod(q,ways)
            for i,x in zip(slots,_unrank(values,k,ways)):
                candidate[i]=x
        if candidate==flat: continue
        ans=test(candidate)
        if ans is not None: return ans
    complete=stats['placements']==total and stats['all_orders_exact']
    return dict(status='no_in_template' if complete else 'unknown',best_tested_width=best,
                reason='template and every sequential order exhausted' if complete else 'bounded search',
                stats=stats)


def native(n,clauses,**caps):
    """Fixed-density root schedule; this is not the arbitrary-density dispatcher."""
    rows=tuple(tuple(c) for c in clauses)
    gates,unused,constant,count=_compile(n,rows)
    if constant is not None:
        if caps.get('pins'): raise ValueError('no physical root to pin')
        return dict(status='constant',raw_count=constant)
    s=max(2,n+count); m=sum(len(ps) for _,ps,_ in gates)
    delta=rounded_power(s)
    plan=SourcePlan(s,m,n+1)
    if max(len(ps) for _,ps,_ in gates)>delta or plan.record is None or m<=plan.record[0]:
        return dict(status='inactive',reason='native direct root')
    a,u=plan.record[2][0]
    return recognize(n,rows,r=64,a=a,u=u,delta=delta,strict=True,**caps)


def execute(n,clauses,*,work_cap,witness=False,**options):
    """Discover first, then contract exactly that slot order. Work cap is for readout."""
    from packet_polynomial_witness import solve,evaluate
    from endpoint_cover_jets import source_rows
    rows=tuple(tuple(c) for c in clauses)
    result=recognize(n,rows,**options)
    if result['status']!='found':
        return result
    kwargs=dict(work_cap=work_cap,packet_order=result['packet_order'])
    if result['pins']:
        gates,unused,_=source_rows(n,rows)
        result['readout']=evaluate(gates,result['packets'],unused=unused,
                                   pins=result['pins'],**kwargs)
        ans=result['readout']
        if witness and ans['status']=='exact' and ans['count']:
            clean=[tuple(sorted(set(c),key=abs)) for c in rows
                   if not any(-x in c for x in c)]
            reps={}
            for c,(_,ports,_) in zip(clean,gates):
                for lit,port in zip(c,ports,strict=True):
                    reps.setdefault(abs(lit),port//2)
            paid=ans['work_bound']
            fixed=dict(result['pins'])
            word=0
            for variable,edge in sorted(reps.items()):
                if edge not in fixed:
                    trial=dict(fixed)
                    trial[edge]=0
                    test=evaluate(gates,result['packets'],unused=unused,pins=trial,
                                  packet_order=result['packet_order'],work_cap=work_cap-paid)
                    if test['status']!='exact':
                        result['readout']=dict(status='unknown',reason='witness_budget',
                                                exact_count=ans['count'],total_work=paid)
                        return result
                    paid+=test['work_bound']
                    fixed[edge]=int(test['count']==0)
                word |= fixed[edge]<<(variable-1)
            if not all(any(bool(word & (1<<(abs(l)-1)))==(l>0) for l in c) for c in rows):
                raise ArithmeticError('physical lift failed raw clause check')
            ans.update(witness=word,total_work=paid)
    else:
        result['readout']=solve(n,rows,result['packets'],witness=witness,**kwargs)
    return result
