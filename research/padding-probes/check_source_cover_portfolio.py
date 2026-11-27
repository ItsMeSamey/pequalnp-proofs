"""Independent small source census and original-label/physical validation."""
import json
from itertools import product
from check_event_tree_native import raw_key, run_machine
from padding_cnf import encode
from stage6_source_solver import compile_source, fixed_dfa


def oracle(clauses, pins):
    names = sorted({abs(x) for row in clauses for x in row} | {v for v,b in pins})
    index = {v:i for i,v in enumerate(names)}
    signs = []
    for row in clauses:
        if any(-x in row for x in row):
            continue
        unique = set(row)
        signs.append((sum(1<<index[abs(x)] for x in unique),
                      sum(1<<index[-x] for x in unique if x<0)))
    good = []
    for w in range(1<<len(names)):
        if all(((w>>index[v])&1) == b for v,b in pins) and all(w&m != b for m,b in signs):
            good.append(w)
    return names,good


def coupled():
    # Equal on the first scope, unequal on the second. No variable is pure.
    rows=[]
    for t in (1,-1):
        rows.extend([(-1,2,t*3),(1,-2,t*3),(1,2,t*4),(-1,-2,t*4)])
    return rows


def wide():
    # Isolate model 001 on the first three coordinates, then make all remaining
    # names occur in both polarities. All 2**13 extensions satisfy the rest.
    rows = [tuple(-j if w>>(j-1)&1 else j for j in (1,2,3)) for w in range(8) if w!=1]
    for j in range(4,17):
        k = 4 + ((j-3) % 13)
        rows.extend([(1,j,k),(1,-j,-k)])
    return rows


def main():
    from source_cover_portfolio import solve
    records = {}
    machine = fixed_dfa()
    def case(label,n,rows,*,pins=(),mode=False,route,expect=None,**options):
        names,good=oracle(rows,pins)
        a=solve(n,rows,source_pins=pins,exact_twice=mode,**options)
        expected = expect or ('SAT' if good else 'UNSAT')
        assert a['status']==expected and a['route']==route, (label,a['status'],a['route'],a['attempts'])
        if expected=='SAT':
            selected=a['true_variables']
            assert selected==tuple(sorted(set(selected))) and set(selected)<=set(names)
            mask=sum(1<<j for j,v in enumerate(names) if v in selected)
            assert mask in good and all((v in selected)==bool(b) for v,b in pins)
            idx={v:i+1 for i,v in enumerate(names)}
            renumber=[tuple(idx[abs(x)] if x>0 else -idx[abs(x)] for x in row) for row in rows]
            job=compile_source(len(names),renumber,exact_twice=mode)
            raw=a['physical']
            assert run_machine(machine,raw)[0]==1
            key=raw_key(raw,job.slots_n)
            assert encode([],job.slots_n,key)==raw and key>>job.slots_n==1
            assert run_machine(machine,encode([],job.slots_n,key^(1<<job.slots_n)))[0]==0
            word=job.lift(raw)
            active={abs(x) for row in renumber for x in row}
            assert all((mask>>(i-1)&1)==(word>>(i-1)&1) for i in active)
        else:
            assert a['true_variables'] is None and a['physical'] is None
        records[label]=[a['status'],a['route'],len(good)]
        return a
    fresh = [(1,-2),(2,3)]
    for stage,limits in [('projected_gaussian',{'exception_cap':64}),
                         ('projected_compressed',{'omission_cap':64}),
                         ('projected_rank2',{'omission_cap':64})]:
        got=case(stage,3,fresh,prepass=False,route='projected',stages=[(stage,limits)],node_cap=0,
                 mode=stage=='projected_rank2')
        assert len(got['attempts'])==1 and got['attempts'][0]['attempts'][0]['stage']==stage
    # An odd cycle plus a chord; the padded clauses are precisely independent sets.
    graph=[(1,2),(2,3),(3,4),(4,5),(5,1),(2,5)]
    hg=[(t,-u,-v) for u,v in graph for t in (6,-6)]
    for label,pins,expected in [('hg-positive',[(3,1)],'SAT'),('hg-adjacent',[(2,1),(5,1)],'UNSAT')]:
        got=case(label,6,hg,pins=pins,stages=(),route='prepass',node_cap=0,expect=expected)
        assert len(got['attempts'])==1
    negative = coupled()
    assert not oracle(negative,())[1]
    for label,rows,expect,cap in [('unsat',negative,'UNSAT',None),
                                  ('capped',negative,'UNKNOWN',0),
                                  ('satisfiable',negative[1:],'SAT',None)]:
        got=case('cover-'+label,4,rows,stages=(),route='cover',expect=expect,node_cap=cap)
        assert [r['route'] for r in got['attempts']]==['prepass','projected','cover']
        assert got['attempts'][0]['method']=='non-renamable'
        m=got['attempts'][-1]['metrics']
        assert (m['nodes']==0 if cap==0 else 0<m['nodes']<=m['node_bound'])
    large=case('cover-radius',16,wide(),stages=(),route='cover',expect='SAT')
    m=large['attempts'][-1]['metrics']
    assert records['cover-radius'][2] == 8192
    assert m['active_variables']==16 and m['radius']==4 and tuple(m['block_lengths'])==(4,4,4,4)
    assert 1 < m['nodes'] <= m['node_bound'] and m['centers_visited'] >= 1
    big=(1<<401)+51
    sparse_rows=[(big,7),(big,-7),(-big,19)]
    case('sparse-cover',big,sparse_rows,pins=[(big-1,1)],prepass=False,stages=(),
         route='cover',expect='SAT',mode=True)
    print(json.dumps(dict(cases=records,radius_metrics=m),sort_keys=True))


if __name__=='__main__':
    main()
