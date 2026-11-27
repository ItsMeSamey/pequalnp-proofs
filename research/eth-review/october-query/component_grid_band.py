"""Exact component product of scaled jet bands, with optional direct local cube crossover."""
from all_grid_cnf_band import evaluate as flat
from extreme_cnf_band import _layout
from extreme_cnf_digit import evaluate as validate
from source_grid_cnf_band import _compile

def _cube_term(forms,pins,order,f,k):
    free=[j for j in range(f) if not pins>>j&1]
    mod=1<<k
    rows=[((row[0]+sum(row[j+1] for j in range(f) if pins>>j&1))%mod,
           tuple(row[j+1]%mod for j in free)) for row in forms]
    d=max(0,len(free)-len(rows))
    shift=order-len(rows)+max(len(rows),len(free))-max(order,f)
    if shift<0: raise ArithmeticError('negative normalization shift')
    if shift>=k: return 0
    mask=(1<<(k+d))-1
    total=0
    for w in range(1<<len(free)):
        term=1
        for a,b in rows:
            term=term*(a+sum(c for j,c in enumerate(b) if w>>j&1))&mask
        total=(total+term)&mask
    if total% (1<<d): raise ArithmeticError('nonintegral cube result')
    return (total>>d)<<shift
from collections import Counter
from itertools import combinations_with_replacement
from extreme_cnf_digit import evaluate as validate_and_first_bit
from extreme_cnf_band import _gate_series, _kernels, _layout, _normalized_term, _product, _rows


def _local_cube(gates,packets,*,center,excess,digits,word_cap=None):
    """For j=r..r+excess return [Z^j]F/2^max(j,f) modulo 2^digits.

    Physical gate format matches extreme_cnf_digit.evaluate. Results omit
    separate unused-variable scalars. word_cap limits baseline assignments.
    """
    if type(excess) is not int or excess < 0 or type(digits) is not int or digits < 1:
        raise ValueError("expected nonnegative excess and positive digit count")
    if word_cap is not None and (type(word_cap) is not int or word_cap < 0):
        raise ValueError("expected a nonnegative word cap")
    gates = tuple((kind,tuple(ps),w) for kind,ps,w in gates)
    packets = tuple(tuple(pk) for pk in packets)
    if not packets or not packets[0]:
        raise ValueError("supply a packet of the actual width")
    length = len(packets[0])
    if type(center) is not int or not -length <= center < length:
        raise ValueError("center outside the grid")
    # The capped validator checks all port incidences; its digit is discarded.
    validate_and_first_bit(gates,packets,center=length-1,word_cap=0)
    m = sum(len(ps) for _,ps,_ in gates)
    successor,live,reads = _layout(packets,center,m)
    live_index = {x:i for i,x in enumerate(live)}
    outside = [x for x in range(m//2) if x not in live_index]
    out_index = {x:i for i,x in enumerate(outside)}
    f = len(outside)
    dormant = [kind == "or" and word == 0 and successor.isdisjoint(ps) for kind,ps,word in gates]
    r = sum(dormant)
    word_count = 1 << len(live)
    info = {"order":r,"outside_bits":f,"live_bits":len(live),"word_bound":word_count}
    if word_cap is not None and word_count > word_cap:
        return dict(info,status="unknown",reason="word_budget")
    count = excess+2
    mod = 1 << digits
    kernels = _kernels(len(packets[0]),center,count,digits)
    answer = [0]*(excess+1)
    for baseline in range(word_count):
        rows = _rows(reads,kernels,live_index,out_index,baseline,count,mod)
        tables = [_gate_series(kind,ps,w,rows,count,mod) for kind,ps,w in gates]
        forms = {i:[tables[i][1].get(0,0)]+[tables[i][1].get(1 << j,0) for j in range(f)]
                 for i in range(len(gates)) if dormant[i]}
        for t in range(excess+1):
            for selection in combinations_with_replacement(range(len(gates)),t):
                special = Counter(selection)
                ordinary = [row for i,row in forms.items() if i not in special]
                weight = 1
                for i in range(len(gates)):
                    if i not in forms and i not in special:
                        weight = weight*tables[i][0].get(0,0) % mod
                if not weight:
                    continue
                coeff = {0:weight}
                for i,d in special.items():
                    coeff = _product(coeff,tables[i][d+int(dormant[i])],mod)
                for pins,value in coeff.items():
                    quotient = _cube_term(ordinary,pins,r+t,f,digits)
                    answer[t] = (answer[t]+value*quotient) % mod
    return dict(info,status="exact",digits=digits,values=tuple(answer),
                first_bit_positions=tuple(max(r+t,f) for t in range(excess+1)))

def evaluate(gates,packets,*,center,excess,digits,word_cap=None,cube_bits=8,fallback=False):
    """word_cap charges summed baseline words on distinct local cache misses.
    cube_bits caps outside-bit dimension for local cube substitution; −1 disables it.
    fallback=True permits the separately word-capped original monolithic routine.
    """
    if not isinstance(excess,int) or excess<0 or not isinstance(digits,int) or digits<1:
        raise ValueError('invalid band')
    if word_cap is not None and (not isinstance(word_cap,int) or word_cap<0): raise ValueError('invalid word cap')
    if cube_bits< -1: raise ValueError('invalid local cube width')
    gates=tuple((kind,tuple(ps),v) for kind,ps,v in gates)
    packets=tuple(tuple(pk) for pk in packets)
    if not packets or not packets[0] or not -len(packets[0])<=center<len(packets[0]):
        raise ValueError('bad packet layout or center')
    validate(gates,packets,center=len(packets[0])-1,word_cap=0)
    m=sum(len(ps) for _,ps,_ in gates)
    parent=list(range(m))
    def root(v):
        while v!=parent[v]:
            parent[v]=parent[parent[v]]
            v=parent[v]
        return v
    def join(group):
        if group:
            a=root(group[0])
            for v in group[1:]:
                b=root(v)
                if a!=b: parent[b]=a
    for _,ps,_ in gates: join(ps)
    for pk in packets: join([i for i in pk if i is not None])
    for i in range(0,m,2): join((i,i+1))
    clusters={}
    for i in range(0,m,2): clusters.setdefault(root(i),[[],[],[]])[0].append(i//2)
    for gate in gates: clusters[root(gate[1][0])][1].append(gate)
    for pk in packets:
        real=next((x for x in pk if x is not None),None)
        if real is not None: clusters[root(real)][2].append(pk)
    R=F=used=hits=0
    result=[1]+[0]*excess
    cache={}
    methods=[]
    for edges,gs,ps in clusters.values():
        mapping={2*g+b:2*i+b for i,g in enumerate(edges) for b in (0,1)}
        g=tuple((k,tuple(mapping[x] for x in xs),w) for k,xs,w in gs)
        p=tuple(tuple(None if x is None else mapping[x] for x in pk) for pk in ps)
        key=g,p
        if key in cache:
            loc,method=cache[key]
            hits+=1
        else:
            _,live,_=_layout(p,center,2*len(edges))
            f=len(edges)-len(live)
            cost=1<<len(live)
            if word_cap is not None and cost>word_cap-used:
                if fallback: return dict(flat(gates,packets,center=center,excess=excess,digits=digits,
                                               word_cap=word_cap),route='monolithic-fallback')
                return dict(status='unknown',reason='component_word_budget',spent_words=used)
            used+=cost
            method='cube' if f<=cube_bits else 'normalized_product'
            loc=(_local_cube if f<=cube_bits else flat)(g,p,center=center,excess=excess,digits=digits,
                                                       word_cap=cost)
            cache[key]=loc,method
        methods.append(method)
        r,f=loc['order'],loc['outside_bits']
        merged=[0]*(excess+1)
        for i,a in enumerate(result):
            for j,b in enumerate(loc['values'][:excess+1-i]):
                s=max(R+i,F)+max(r+j,f)-max(R+r+i+j,F+f)
                if s<0: raise ArithmeticError('invalid component normalization')
                if s<digits: merged[i+j]=(merged[i+j]+((a*b)<<s))% (1<<digits)
        result=merged
        R+=r
        F+=f
    return dict(status='exact',route='component',order=R,outside_bits=F,live_bits=m//2-F,
                values=tuple(result),digits=digits,first_bit_positions=tuple(max(R+i,F) for i in range(excess+1)),
                components=len(clusters),spent_words=used,cache_hits=hits,methods=tuple(methods))

def supplied(n,clauses,packets,**options):
    gates,unused,constant,_=_compile(n,clauses)
    if constant is not None: return dict(status='constant',raw_count=constant)
    return dict(evaluate(gates,packets,**options),unused_raw_bits=unused)
