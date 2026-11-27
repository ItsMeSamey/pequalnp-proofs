"""Recover affine AND factors using identities in the squarefree Boolean ring."""
from pathlib import Path
import sys
from itertools import permutations,product
from time import perf_counter_ns
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'direct-sat-successor'))
from successor import portfolio
sys.path.insert(0,str(ROOT/'two-order-proposer'))
import proposer


def bits(mask):
    while mask:
        b=mask&-mask
        yield b
        mask^=b


def affine(mask):
    return {b if b!=1 else 0 for b in bits(mask)}


def multiply(a,b):
    result=set()
    for x in affine(a):
        for y in affine(b):
            result.symmetric_difference_update([x|y])
    return result


def expand(n,gates,output,chosen):
    poly=affine(output)
    for j in chosen:
        poly.symmetric_difference_update([1<<(1+n+j)])
        poly.symmetric_difference_update(multiply(*gates[j]))
    return poly


def verify(n,gates,output,cert):
    gates=portfolio.validate(n,gates,output)
    sites=cert['expand']
    if len(set(sites))!=len(sites) or any(type(j) is not int or not 0<=j<len(gates) for j in sites):
        return False
    operands=cert['forms']
    if len(operands)!=2 or any(type(a) is not int or a<0 or a.bit_length()>1+n+len(gates) for a in operands):
        return False
    return expand(n,gates,output,sites)==multiply(*operands)


def factors(poly):
    rows={}
    for term in poly:
        if term.bit_count()!=2:continue
        x=term&-term;y=term^x
        rows[x]=rows.get(x,0)^y
        rows[y]=rows.get(y,0)^x
    if not rows:return
    a=next(iter(rows.values()))
    b=next((v for v in rows.values() if v!=a),None)
    if b is None or any(v not in (a,b,a^b) for v in rows.values()):return
    # All ordered bases of the rank-two polar row space and all affine shifts.
    for u,v in permutations((a,b,a^b),2):
        for c,d in product(range(2),repeat=2):
            if multiply(u^c,v^d)==poly:
                yield u^c,v^d


def discover(n,gates,output):
    gates=portfolio.validate(n,gates,output)
    live=[b.bit_length()-n-2 for b in bits(output) if b.bit_length()>n+1]
    tried=set()
    for chosen in [tuple(live)]+[(j,) for j in live]:
        if chosen in tried:continue
        tried.add(chosen)
        for forms in factors(expand(n,gates,output,chosen)):
            cert=dict(expand=chosen,forms=forms)
            if not verify(n,gates,output,cert):raise AssertionError('identity certificate failed')
            return cert
    return None


def solve(n,gates,output,**options):
    start=perf_counter_ns()
    gates=portfolio.validate(n,gates,output)
    cert=discover(n,gates,output)
    ticks=perf_counter_ns()-start
    if cert is None:return dict(status='skip',reason='no factor certificate',elapsed_ns=ticks)
    new=gates+(tuple(cert['forms']),)
    result=proposer.solve(n,new,1<<(n+len(new)),**options)
    if result['status']=='sat' and not portfolio.evaluate(n,gates,output,result['witness']):
        raise AssertionError('untouched witness replay failed')
    return dict(**result,certificate=cert,preprocessing_ns=ticks,elapsed_ns=perf_counter_ns()-start)
