"""Normalized residue blocks at consecutive orders of a signed OR/COPY root."""
from itertools import combinations_with_replacement
from collections import Counter
from all_center_packet_jets import JetRing
from packet_entry_tape import Ring
from variable_packet_machine import shifted_kernel
from normalized_affine_digits import normalized_product
from extreme_cnf_digit import evaluate as validate_and_first_bit


def _accumulate(out,mask,value,mod):
    weight = (out.get(mask,0) + value) % mod
    if weight:
        out[mask] = weight
    else:
        out.pop(mask,None)


def _product(a,b,mod):
    out = {}
    for u,x in a.items():
        for v,y in b.items():
            _accumulate(out,u|v,x*y,mod)
    return out


def _series_product(a,b,mod):
    out = [{} for _ in a]
    for i,x in enumerate(a):
        for j,y in enumerate(b[:len(a)-i]):
            for mask,weight in _product(x,y,mod).items():
                _accumulate(out[i+j],mask,weight,mod)
    return out


def _gate_series(kind,ports,word,rows,count,mod):
    def initial():
        return [{0:1}] + [{} for _ in range(count-1)]
    def term(fixed):
        out = initial()
        for i,row in enumerate(ports):
            factors = rows[row]
            if not (fixed >> i) & 1:
                factors = [{m:-c for m,c in layer.items()} for layer in factors]
                _accumulate(factors[0],0,1,mod)
            out = _series_product(out,factors,mod)
        return out
    if kind == "copy":
        out = term(0)
        other = term((1 << len(ports))-1)
        scale = 1
    else:
        out = initial()
        other = term(word)
        scale = -1
    for layer,add in zip(out,other):
        for m,c in add.items():
            _accumulate(layer,m,scale*c,mod)
    return out


def _kernels(length,center,count,k):
    work = JetRing(Ring(k+count-1,(0,),1),count)
    point = (0,1) + (0,)*(count-2)
    out = {}
    for d in range(1-length,length):
        raw = shifted_kernel(work,length,center,point,d)
        if any(value % (1 << j) for j,value in enumerate(raw)):
            raise ArithmeticError("illegal kernel slope")
        out[d] = tuple((v >> j) % (1 << k) for j,v in enumerate(raw))
    return out

def _layout(packets,center,m):
    successor = set()
    live = set()
    reads = [[] for _ in range(m)]
    for pk in packets:
        for i,row in enumerate(pk):
            if row is None:
                continue
            j = i+center
            if 0 <= j < len(pk) and pk[j] is not None:
                successor.add(row)
                live.add(pk[j]//2)
            reads[row] = [(col//2,j-i) for j,col in enumerate(pk) if col is not None]
    return successor,sorted(live),reads


def _rows(reads,kernels,live_index,out_index,baseline,count,mod):
    rows = []
    for values in reads:
        layers = [{} for _ in range(count)]
        for index,d in values:
            if index in live_index:
                if not (baseline >> live_index[index]) & 1:
                    continue
                mask = 0
            else:
                mask = 1 << out_index[index]
            for j,c in enumerate(kernels[d]):
                _accumulate(layers[j],mask,c,mod)
        rows.append(layers)
    return rows


def _normalized_term(forms,pins,order,f,k):
    free = [j for j in range(f) if not (pins >> j) & 1]
    pinned = [j for j in range(f) if (pins >> j) & 1]
    shift = order-len(forms)+max(len(forms),len(free))-max(order,f)
    if shift < 0:
        raise ArithmeticError("invalid order normalization")
    if shift >= k:
        return 0
    restricted = []
    for row in forms:
        offset = row[0]+sum(row[j+1] for j in pinned)
        restricted.append([offset]+[row[j+1] for j in free])
    return normalized_product(restricted,len(free),k-shift) << shift


def evaluate(gates,packets,*,center,excess,digits,word_cap=None):
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
    validate_and_first_bit(gates,packets,center=center,word_cap=0)
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
                    quotient = _normalized_term(ordinary,pins,r+t,f,digits)
                    answer[t] = (answer[t]+value*quotient) % mod
    return dict(info,status="exact",digits=digits,values=tuple(answer),
                first_bit_positions=tuple(max(r+t,f) for t in range(excess+1)))
