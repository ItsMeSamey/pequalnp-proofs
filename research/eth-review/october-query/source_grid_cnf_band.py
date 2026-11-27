"""Normalized native-root jet slices from signed, declared CNFs."""
from endpoint_cover_jets import source_rows
from packet_layout import SourcePlan, rounded_power
from all_grid_cnf_band import evaluate
from extreme_cnf_band import _layout


def _compile(n,clauses):
    if type(n) is not int or n < 0:
        raise ValueError("invalid number of declared variables")
    clauses = tuple(tuple(c) for c in clauses)
    if any(type(x) is not int or not 1 <= abs(x) <= n for c in clauses for x in c):
        raise ValueError("invalid signed literal")
    physical,unused,constant = source_rows(n,clauses)
    gates = []
    for kind,ports,signs in physical:
        false_word = sum((1-s) << j for j,s in enumerate(signs)) if kind == "or" else None
        gates.append((kind,ports,false_word))
    return tuple(gates),unused,constant,len(clauses)


def supplied(n,clauses,packets,*,center,excess,digits,word_cap=None):
    """Actual source compiler and a supplied port layout, bypassing the native schedule."""
    gates,unused,constant,_ = _compile(n,clauses)
    if constant is not None:
        return {"status":"constant","raw_count":constant}
    result = evaluate(gates,packets,center=center,excess=excess,digits=digits,word_cap=word_cap)
    return dict(result,unused_raw_bits=unused)


def native(n,clauses,*,center,excess,digits,word_cap=None):
    """Source's own root plan, active centers only. Digits are for the used-variable root.

    Values are residues at the returned orders, normalized by the stated bit
    positions. An inactive original recursion has no native jet at that point.
    Unused declared variables are restored only after native reconstruction.
    """
    if type(center) is not int or type(excess) is not int or excess < 0:
        raise ValueError("expected integer center and nonnegative excess")
    if type(digits) is not int or digits < 1:
        raise ValueError("expected a positive digit width")
    if word_cap is not None and (type(word_cap) is not int or word_cap < 0):
        raise ValueError("invalid baseline-word budget")
    gates,unused,constant,clause_count = _compile(n,clauses)
    if constant is not None:
        return {"status":"constant","raw_count":constant}
    s = max(2,n+clause_count)
    m = sum(len(ps) for _,ps,_ in gates)
    if max(len(ps) for _,ps,_ in gates) > rounded_power(s):
        return {"status":"inactive","reason":"native_degree_fallback"}
    planner = SourcePlan(s,m,n+1)
    if planner.record is None or m <= planner.record[0]:
        return {"status":"inactive","reason":"native_direct_root"}
    a,u = planner.record[2][0]
    length = 1 << a
    if not -length <= center < length or center == 0:
        return {"status":"inactive","reason":"omitted_center"}
    i = (abs(center) & -abs(center)).bit_length()-1
    if i >= u:
        return {"status":"inactive","reason":"omitted_center"}
    # SourcePlan's conditional expectation only reads the original ordered port lists.
    net = ([(None,ps) for _,ps,_ in gates],[(None,(2*j,2*j+1)) for j in range(m//2)])
    _,_,packets,_ = planner(net,m,0)
    successor,live,_ = _layout(packets,center,m)
    r = sum(kind == "or" and w == 0 and successor.isdisjoint(ps) for kind,ps,w in gates)
    f = m//2-len(live)
    h = (3*m+u-1)//u
    pt = n+1+8*h*(length >> i)+8*m*(a+1)
    last = min(r+excess,h*(u-i)-1)
    common = {"precision":pt,"native_orders":h*(u-i),"order":r,"unused_raw_bits":unused}
    if last < r:
        return dict(common,status="exact",values=(),first_bit_positions=(),digit_counts=())
    positions = tuple(max(j,f) for j in range(r,last+1))
    counts = tuple(max(0,min(digits,pt-pos)) for pos in positions)
    if not counts[0]:
        return dict(common,status="exact",values=(0,)*len(counts),first_bit_positions=positions,
                    digit_counts=counts)
    fixed = evaluate(gates,packets,center=center,excess=last-r,digits=counts[0],word_cap=word_cap)
    if fixed["status"] == "unknown":
        return dict(fixed,**{"precision":pt,"native_orders":h*(u-i),"unused_raw_bits":unused})
    return dict(common,status="exact",values=tuple(v % (1 << bits) for v,bits in zip(fixed["values"],counts)),
                first_bit_positions=positions,digit_counts=counts,live_bits=len(live),outside_bits=f)
