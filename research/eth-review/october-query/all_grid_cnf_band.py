"""Signed OR/COPY normalized coefficient bands at every grid center, T=t+2LZ."""
from collections import Counter
from itertools import combinations_with_replacement
from extreme_cnf_digit import evaluate as validate_and_first_bit
from extreme_cnf_band import _gate_series, _kernels, _layout, _normalized_term, _product, _rows


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
                    quotient = _normalized_term(ordinary,pins,r+t,f,digits)
                    answer[t] = (answer[t]+value*quotient) % mod
    return dict(info,status="exact",digits=digits,values=tuple(answer),
                first_bit_positions=tuple(max(r+t,f) for t in range(excess+1)))
