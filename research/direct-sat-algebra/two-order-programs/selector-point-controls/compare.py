from instances import original
import json,sys
from time import perf_counter_ns
sys.path[:0]=['/workspace/scratch/selector-point-syndrome','/workspace/scratch/selector-fd-clock']
from fd_clock import accepts_cnf,solve_cnf as old
from point_solver import solve_cnf as new
for h in (3,5,9):
    for yes in (False,True):
        if len(sys.argv)>1 and (h,int(yes)) != tuple(map(int,sys.argv[1:])):
            continue
        n,rows=original(h,yes)
        jobs=[('fd',old,dict(key_bound_cap=256))]
        for d in (3,2):
            jobs.append((f'point{d}',new,dict(codim_cap=d,oracle_call_cap=100000,closure_seed_cap=1000000)))
        for name,solver,kwargs in jobs:
            start=perf_counter_ns()
            ans=solver(n,(iter(row) for row in rows),**kwargs)
            ns=perf_counter_ns()-start
            if name!='point3':
                assert ans['status']=='skip',ans
            elif ans['status']!='skip':
                assert ans['status']==('sat' if yes else 'unsat'),ans
                if yes:
                    x=ans['witness']
                    assert accepts_cnf(rows,x)
                    assert all(((x>>(3*h+i))&1)==(i%h==h//2) for i in range(3*h))
            print(json.dumps(dict(h=h,yes=yes,route=name,n=n,clauses=len(rows),elapsed_ns=ns,**ans)),flush=True)
