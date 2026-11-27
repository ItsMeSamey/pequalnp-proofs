"""Capped exact native AND decision; input orders proposed or supplied."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
for folder in ('two-order-proposer','direct-sat-algebra','direct-sat-portfolio'):
    sys.path.insert(0,str(ROOT/folder))
from proposer import cone_orders
from native_intersection import trim,evaluate
from factor_compiler import compile_factor
from backward_reset_peel import peel,intersect_witness
from two_order_semantic_labels import recognize as fixed
from two_state_any_order import recognize as any_order
from two_state_other_order import solve as intersect
from original_cnf import compile_cnf,accepts_cnf


def solve(n,gates,output,*,orders=None,cell_cap=250000,rank_cap=32,
          peel_steps=100000,cell_pairs=10000,linear_work=10000000):
    if min(n,cell_cap,rank_cap,peel_steps,cell_pairs,linear_work)<0:
        raise ValueError('invalid limits')
    gates=tuple(gates)
    if output<0 or output.bit_length()>n+1+len(gates):raise ValueError('invalid output')
    for j,(a,b) in enumerate(gates):
        if min(a,b)<0 or (a|b).bit_length()>n+j+1:raise ValueError('invalid operands')
    if orders is not None and (len(orders)!=2 or any(sorted(o)!=list(range(n)) for o in orders)):
        raise ValueError('invalid orders')
    cost={'raw_bits':n,'gates':len(gates),'factor_calls':[],'label_calls':[],'declines':[]}
    def finish(status,route,witness=None):
        ans={'status':status,'route':route,'cost':cost}
        if status=='sat':
            if not evaluate(n,gates,output,witness):raise AssertionError('original replay mismatch')
            ans['witness']=witness
        return ans
    root=output.bit_length()-n-2
    if output.bit_length()<=n+1:
        if output&1:return finish('sat','affine readout',0)
        if not output:return finish('unsat','affine readout')
        return finish('sat','affine readout',((output&-output)>>1))
    if root<0 or output.bit_count()!=1:return finish('skip','unsupported readout')
    live=[trim(n,gates[:root],form) for form in gates[root]]
    # A single surviving branch decreases latest gate index every iteration.
    # Credit operand-reduction and pivot-scan work separately from word bit length.
    peel_bound=sum((len(net)+1)*32*(n+1) for net,_ in live)
    cost['peel_work_bound']=peel_bound
    if peel_bound<=peel_steps:
        flats=[peel(n,net,form) for net,form in live]
        cost['cell_sizes']=[None if h is None else len(h) for h in flats]
        if any(h==[] for h in flats):return finish('unsat','empty accepting cells')
        if all(h is not None for h in flats):
            product=len(flats[0])*len(flats[1])
            cost['cell_pair_bound']=product
            if product<=cell_pairs:
                x=intersect_witness(*flats)
                return finish('unsat' if x is None else 'sat','affine-cell intersection',x)
    if orders is None:
        orders=[cone_orders(n,gates[:root],f)[0][0] for f in gates[root]]
    cost['orders']=orders
    programs=[]
    for i,((net,form),order) in enumerate(zip(live,orders)):
        cap=cell_cap//2+(cell_cap%2 if i==1 else 0)
        r=compile_factor(n,net,form,order=order,rank_cap=rank_cap,budget=cap)
        cost['factor_calls'].append(dict(live=len(net),cap=cap,detail=r['cost']))
        if r['status']!='complete':return finish('skip','factor cap')
        programs.append(r['program'])
    left=linear_work
    def debit(kind,i,amount):
        nonlocal left
        if amount>left:
            cost['declines'].append((kind,i,amount));return False
        left-=amount
        cost['label_calls'].append(dict(kind=kind,side=i,allocation=amount))
        return True
    for kind in ('fixed','any'):
        for i,p in enumerate(programs):
            w=max(p[0]);u=max(programs[1-i][0])
            # Charges count candidate scans; dense apply, row operations and
            # index/witness storage have additional polynomial bit cost.
            bound=(2*n*w+4*n+2) if kind=='fixed' else (n*(n+1)//2)*2*n*(2*w+1)+1
            if not debit(kind,i,bound):continue
            if kind=='fixed':
                det,receipt=fixed(p,orders[i])
                chosen=orders[i]
            else:
                det,chosen,receipt=any_order(p,orders[i])
            cost['label_calls'][-1]['actual']=receipt
            if det is None:continue
            if not debit('joint',i,(n+1)*n*max(4*u,2)+1):continue
            r=intersect(det,chosen,programs[1-i],orders[1-i])
            cost['label_calls'][-1]['actual']=r['cost']
            return finish(r['status'],kind+' order',r.get('witness'))
    return finish('skip','no completed intersection')


def solve_cnf(n,clauses,**kwargs):
    clauses=tuple(tuple(c) for c in clauses)
    gates,output=compile_cnf(n,clauses)
    r=solve(n,gates,output,**kwargs)
    if r['status']=='sat' and not accepts_cnf(clauses,r['witness']):
        raise AssertionError('source CNF replay mismatch')
    return r
