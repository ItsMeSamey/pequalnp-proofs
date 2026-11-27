"""Exact native conjunction under independently supplied original-bit orders."""
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'compression'))
from boolean_value_automata import dot,indices
from implicit_wire_circuit import solve as same_order
from two_order_semantic_labels import intersection
from factor_compiler import compile_factor


def trim(n,gates,output):
    needed=output
    keep=[]
    for j in reversed(range(len(gates))):
        if needed>>(n+1+j)&1:
            keep.append(j)
            a,b=gates[j]
            needed|=a|b
    low=(1<<(n+1))-1
    mapping={}
    def translate(row):
        result=row&low
        for i in indices(row&~low):
            result|=1<<mapping[i]
        return result
    live=[]
    for j in reversed(keep):
        live.append(tuple(translate(x) for x in gates[j]))
        mapping[n+1+j]=n+len(live)
    return tuple(live),translate(output)


def evaluate(n,gates,out,word):
    bits=1|(word<<1)
    for j,(a,b) in enumerate(gates):
        bits|=(dot(a,bits)&dot(b,bits))<<(n+1+j)
    return dot(out,bits)


def solve(n,gates,output,orders,*,budget=1000000,rank_cap=256,fallback=True):
    if n<0 or budget<0 or rank_cap<0 or len(orders)!=2:raise ValueError('invalid bounds')
    for order in orders:
        if sorted(order)!=list(range(n)):raise ValueError('invalid original input order')
    if output<0 or output.bit_length()>n+1+len(gates):raise ValueError('invalid readout')
    for j,(a,b) in enumerate(gates):
        if min(a,b)<0 or max(a,b).bit_length()>n+j+1:raise ValueError('invalid gate')
    # Budget slices are never reused, even after a failed compilation.
    share=budget//(3 if fallback else 2)
    cost={'raw_bits':n,'original_gates':len(gates),'factor_caps':[share,share],
          'fallback_cap':budget-2*share if fallback else 0,'factors':[]}
    root=output.bit_length()-n-2
    reason='output is not a positive single native AND gate'
    if output.bit_count()==1 and root>=0:
        programs=[]
        for row,order in zip(gates[root],orders):
            live,form=trim(n,gates[:root],row)
            r=compile_factor(n,live,form,order=order,budget=share,rank_cap=rank_cap)
            cost['factors'].append(dict(live_gates=len(live),status=r['status'],**r['cost']))
            if r['status']!='complete':
                reason='factor compilation cap'
                break
            programs.append(r['program'])
        if len(programs)==2:
            result=intersection(programs[0],orders[0],programs[1],orders[1])
            cost['label_checks']=result['label_checks']
            if result['status']!='skip':
                if result['status']=='sat' and not evaluate(n,gates,output,result['witness']):
                    raise AssertionError('original circuit witness mismatch')
                cost['joint']=result['cost']
                result['cost']=cost
                result['route']='two-order'
                return result
            reason='both factor orders exceed two residual labels'
    if fallback:
        result=same_order(n,gates,output,order=orders[0],budget=cost['fallback_cap'],rank_cap=rank_cap)
        cost['fallback']=result['cost']
        cost['primary_decline']=reason
        result['cost']=cost
        result['route']='same-order fallback'
        return result
    return {'status':'skip','reason':reason,'cost':cost}
