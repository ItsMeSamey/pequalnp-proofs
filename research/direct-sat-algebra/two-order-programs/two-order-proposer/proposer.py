"""Deterministic candidate input orders; each answer is certified on the original circuit."""
from collections import Counter
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'two-order-native'))
from native_intersection import solve as certify,trim
from boolean_value_automata import indices

def cone_orders(n,gates,form):
    live,out=trim(n,gates,form)
    raw=(1<<(n+1))-2
    seen={}; controls=Counter(); probes=0
    for a,b in live:
        for expr,other in ((a,b),(b,a)):
            for r in indices(expr&raw):
                probes+=1
                seen.setdefault(r-1,None)
            mask=expr>>1
            if mask and expr.bit_length()<=n+1 and (other>>1).bit_count()>=2:
                controls[mask]+=1
    for r in indices(out&raw):
        probes+=1;seen.setdefault(r-1,None)
    chronology=tuple(seen)+tuple(i for i in range(n) if i not in seen)
    frequency=sorted(controls,key=lambda m:(-controls[m],m.bit_count(),m))
    head={}
    for m in frequency:
        for i in indices(m):head.setdefault(i,None)
    mux=tuple(head)+tuple(i for i in chronology if i not in head)
    repeated=bool(frequency and controls[frequency[0]]>=2)
    choices=[mux if repeated else chronology,chronology,tuple(range(n)),mux,tuple(reversed(chronology))]
    return list(dict.fromkeys(choices)),dict(live_gates=len(live),raw_incidences=probes,
                                              candidate_forms=len(controls),repeated_selector=repeated)

def solve(n,gates,output,*,budget=250000,rank_cap=24,max_attempts=4):
    if n<0 or budget<0 or rank_cap<0 or max_attempts<1:raise ValueError('invalid limits')
    gates=tuple(gates)
    if output<0 or output.bit_length()>n+len(gates)+1:raise ValueError('invalid output')
    for j,(a,b) in enumerate(gates):
        if min(a,b)<0 or max(a,b).bit_length()>n+j+1:raise ValueError('invalid operands')
    root=output.bit_length()-n-2
    if output.bit_count()!=1 or root<0:
        return {'status':'skip','reason':'requires a positive single gate readout'}
    (left,lcost),(right,rcost)=[cone_orders(n,gates[:root],f) for f in gates[root]]
    pairs=sorted(((i,j) for i in range(len(left)) for j in range(len(right))),
                 key=lambda ij:(sum(ij),max(ij),ij))[:max_attempts]
    cost={'raw_bits':n,'gates':len(gates),'proposal':[lcost,rcost],'attempts':[]}
    remaining=budget
    for h,(i,j) in enumerate(pairs):
        if not remaining:break
        cap=remaining if h+1==len(pairs) else (remaining+1)//2
        remaining-=cap
        r=certify(n,gates,output,(left[i],right[j]),budget=cap,rank_cap=rank_cap,fallback=False)
        cost['attempts'].append(dict(orders=[left[i],right[j]],cap=cap,status=r['status'],
                                     receipt=r['cost'],reason=r.get('reason')))
        if r['status']!='skip':
            answer={'status':r['status'],'cost':cost}
            if 'witness' in r:answer['witness']=r['witness']
            return answer
    return {'status':'skip','reason':'no proposed pair completed within limits','cost':cost}
