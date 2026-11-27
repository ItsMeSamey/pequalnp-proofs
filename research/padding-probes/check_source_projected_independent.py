"""Check the contracted positive chart on original clauses and original bytes."""
import json
from stage6_source_solver import compile_source, fixed_dfa
from stage6_positive_projection import solve_positive
from stage6_projected_solver import solve
from check_event_tree_native import raw_key, run_machine


def check(label, n, clauses, pins, mode, stage, caps):
    models = {x for x in range(1 << n) if all((x>>(i-1))&1 == b for i,b in pins)
              and all(any(((x>>(abs(l)-1))&1) == (l>0) for l in row) for row in clauses)}
    response = solve(n,clauses,source_pins=pins,exact_twice=mode,
                     stages=[(stage,caps)],fallback_limit=0)
    attempt, = response['attempts']
    assert attempt['stage']==stage and response['status']==('SAT' if models else 'UNSAT'), (label,response)
    job = compile_source(n,clauses,exact_twice=mode)
    decision, mask, evidence = solve_positive(job,dict(pins),stage,caps)
    assert decision==response['status']
    if stage in ('projected_compressed','projected_rank2'):
        assert evidence['counts'] == {0:0,1:len(models)}, (label,evidence['counts'])
    if models:
        raw = response['physical']
        assert mask in models and response['witness'] in models
        assert run_machine(fixed_dfa(),raw)[0] == 1
        assert raw_key(raw,job.slots_n)>>job.slots_n == 1
        assert job.lift(raw)==response['witness'] and job.word(response['witness'])==raw
    else:
        assert response['physical'] is None and response['witness'] is None
    return len(models)


def main():
    stages = {'projected_gaussian':dict(exception_cap=128,branch_cap=4096),
              'projected_compressed':dict(omission_cap=128,state_cap=128,work_cap=8192),
              'projected_rank2':dict(omission_cap=128,codimension_cap=8)}
    results = {}
    for stage, opts in stages.items():
        vals = []
        for mode in (False,True):
            vals.append(check('signed strict',3,[(1,-2,3)],[(1,1)],mode,stage,opts))
            vals.append(check('binary OR',2,[(1,2)],[],mode,stage,opts))
            vals.append(check('four incompatible rows',2,[(1,2),(1,-2),(-1,2),(-1,-2)],
                              [],mode,stage,opts))
        assert vals == [4,3,0] * 2
        results[stage]=vals
    print(json.dumps(results,sort_keys=True))


if __name__=='__main__':
    main()
