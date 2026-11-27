"""Source-first exact/capped CNF dispatch on declared Boolean variables."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from time import perf_counter_ns

ROOT=Path(__file__).resolve().parents[1]


def load(name,path):
    spec=spec_from_file_location(name,ROOT/path)
    mod=module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


source=load('_combined_original_first','guard-cap-review/cnf-two-state/source_routes/first.py')
native=load('_combined_original_successor','two-order-successor/successor.py')


def solve_cnf(n,clauses,*,complete=False,fallback_limit=0,cell_cap=250000,rank_cap=32,
              peel_steps=100000,cell_pairs=10000,linear_work=10000000):
    started=perf_counter_ns()
    if type(n) is not int or n<0 or type(complete) is not bool:
        raise ValueError('invalid variable count or completion flag')
    budget=dict(fallback_limit=fallback_limit,cell_cap=cell_cap,rank_cap=rank_cap,
                peel_steps=peel_steps,cell_pairs=cell_pairs,linear_work=linear_work)
    if any(type(v) is not int or v<0 for v in budget.values()):
        raise ValueError('budgets must be nonnegative integers')
    raw=tuple(tuple(c) for c in clauses)
    if any(type(l) is not int or not 1<=abs(l)<=n for c in raw for l in c):
        raise ValueError('literal outside declared original bits')
    cost={'n':n,'clauses':len(raw),'literals':sum(map(len,raw)),'complete':complete,
          'budgets':budget,'stages':[],'fallback_assignments':0}
    def log(stage,status,route,start,details):
        cost['stages'].append(dict(stage=stage,status=status,route=route,
                                   elapsed_ns=perf_counter_ns()-start,details=details))
    def finish(status,route,w=None):
        result={'status':status,'route':route,'cost':cost}
        if status=='sat':
            if type(w) is not int or w<0 or w.bit_length()>n or not native.accepts_cnf(raw,w):
                raise AssertionError('original source replay failed')
            result['witness']=w
        cost['total_elapsed_ns']=perf_counter_ns()-started
        return result
    start=perf_counter_ns()
    verdict,route,w=source.fast(n,raw,fallback=None)
    status=verdict.lower()
    log('source',status,route,start,{})
    if status!='skip':return finish(status,route,w)
    start=perf_counter_ns()
    r=native.solve_cnf(n,raw,cell_cap=cell_cap,rank_cap=rank_cap,peel_steps=peel_steps,
                       cell_pairs=cell_pairs,linear_work=linear_work)
    log('native',r['status'],r['route'],start,r['cost'])
    if r['status']!='skip':return finish(r['status'],r['route'],r.get('witness'))
    start=perf_counter_ns()
    total=1<<n
    limit=total if complete else min(total,fallback_limit)
    for x in range(limit):
        cost['fallback_assignments']+=1
        if native.accepts_cnf(raw,x):
            log('exhaustive','sat','original enumeration',start,{'limit':limit})
            return finish('sat','original enumeration',x)
    status='unsat' if limit==total else 'skip'
    log('exhaustive',status,'original enumeration',start,{'limit':limit})
    return finish(status,'original enumeration')
