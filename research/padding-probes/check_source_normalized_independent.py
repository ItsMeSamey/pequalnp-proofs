"""Separate normalized successor. Compare canonical originals with source counts."""
from itertools import product
import json
from check_event_tree_native import raw_key, run_machine
from padding_cnf import encode
from stage6_source_solver import compile_source, fixed_dfa
from stage6_normalized_solver import solve


def census(clauses,n,twice):
    chart = compile_source(n,clauses,exact_twice=twice)
    machine = fixed_dfa()
    fixed = chart.dummy_bits
    names = sorted({abs(a) for a in chart.aliases} - fixed.keys())
    assert len(fixed) == (3 if twice else 6) * len(clauses)
    assert set(fixed.values()) <= {0 if twice else 1}
    words = {}
    for bits in product((0,1),repeat=len(names)):
        values = {**fixed, **dict(zip(names,bits))}
        key = sum((values[abs(a)] ^ int(a<0)) << i for i,a in enumerate(chart.aliases))
        raw = encode([],chart.slots_n,key)
        if run_machine(machine,raw)[0]:
            mask = chart.lift(raw)
            assert mask not in words
            assert all(any(((mask>>(abs(l)-1))&1)==(l>0) for l in row) for row in clauses)
            assert raw == chart.word(mask) and raw_key(raw,chart.slots_n)==key
            words[mask]=raw
    return chart,words


def relative():
    from event_relative_compile import compile_factors
    from event_affine_compile import compile_factors as absolute
    from event_field_codes import field_codebooks
    import event_macro
    ds = {'x':(0,1,2),'y':(0,1,2),'bit':(0,1)}
    cs = [('x','y',{(0,0),(1,1),(2,2)})]
    a = compile_factors(ds,cs,'bit',omission_cap=2)
    assert a['status']=='ok' and a['metrics']['relative_holes']==0
    assert absolute(ds,cs,'bit',omission_cap=2)['status']=='unknown'
    survivors = set()
    for w in range(1 << a['width']):
        if all((w & m).bit_count()%2 == b for m,b in a['equations']) and all(
                w & m != b for m,b in a['cylinders']):
            survivors.add(tuple((w>>a['offset'][v]) & ((1<<a['widths'][v])-1) for v in ds))
    assert survivors == {(x,x,b) for x,b in product(range(3),range(2))}
    f = compile_source(0,[])
    table,initial,bottom,outputs = fixed_dfa()
    ev = event_macro.build([],f.slots_n,f.aliases,table,initial,bottom,outputs)
    books = field_codebooks(table,outputs,bottom)(ev)
    system = compile_factors(ev.domains,ev.constraints,ev.output,codebooks=books)
    assert system['status']=='ok' and system['metrics']['relative_holes']==0
    for row, bit in product(ev.domains[0], ev.domains[1]):
        word = books[0][row] | (books[1][bit]<<system['offset'][1])
        feasible = all((word&m).bit_count()%2==b for m,b in system['equations'])
        feasible &= all(word&m!=b for m,b in system['cylinders'])
        assert feasible == (row.bit == bit)
    return len(survivors)


def main():
    rows = {}
    for twice in (False,True):
        for n,clauses in [(0,[]),(3,[(1,-2,3)])]:
            chart,words = census(clauses,n,twice)
            expected = set(range(1<<n)) - ({2} if clauses else set())
            assert set(words)==expected
            source_n = n+2
            public = solve(source_n,clauses,exact_twice=twice,source_pins=[(source_n,1)],
                           stages=[('block',{'state_cap':None,'step_cap':None})],fallback_limit=8)
            assert public['status']=='SAT'
            mask = public['witness']
            assert words[mask & ((1<<n)-1)] == public['physical']
            assert public['sparse_witness'] == tuple(j+1 for j in range(source_n) if (mask>>j)&1)
            assert source_n in public['sparse_witness'] and public['dummy_pins']==len(chart.dummy_bits)
            rows[str((twice,n))] = len(words)
    assert relative()==6
    from stage6_sparse_source import solve as sparse
    n = (1<<400)+17
    for clauses,pins,expected in [([(n,)],[(n-1,1)],(n-1,n)),([],[],()), ([(n,),(-n,)],[],None)]:
        result = sparse(n,clauses,source_pins=pins,stages=(),fallback_limit=None)
        assert result['status']==('UNSAT' if expected is None else 'SAT')
        assert result['true_variables']==expected and 'witness' not in result
    for stage in ('gaussian','compressed','rank2'):
        for n,clauses,pins in [(0,[],[]),(3,[(1,-2,3)],[(1,1),(2,0),(3,0)])]:
            attempt = solve(n,clauses,source_pins=pins,stages=[stage],fallback_limit=0)
            if not clauses:
                assert attempt['status']=='SAT'
            assert attempt['status'] in ('SAT','UNKNOWN')
            assert attempt['attempts'][0]['stage']==stage
            if attempt['status']=='SAT':
                assert len(attempt['attempts'])==1
                chart=compile_source(n,clauses)
                assert chart.word(attempt['witness'])==attempt['physical']
                assert run_machine(fixed_dfa(),attempt['physical'])[0]==1
            else:
                assert attempt['attempts'][0]['status']=='unknown' and attempt['attempts'][-1]['examined']==0
            rows[stage+'-'+str(len(clauses))]=attempt['status']
    print(json.dumps(rows,sort_keys=True))


if __name__=='__main__':
    main()
