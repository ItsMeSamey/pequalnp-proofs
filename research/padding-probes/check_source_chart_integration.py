"""Independent truth-table oracle and physical replay for the GS/source integration."""
import json

from check_source_cover_portfolio import oracle
from check_event_tree_native import raw_key, run_machine
from padding_cnf import encode
from source_easy_prepass import solve_prepass
from stage6_source_solver import compile_source, fixed_dfa


def xor_zero(names):
    return [tuple(-v if pattern >> j & 1 else v for j, v in enumerate(names))
            for pattern in range(8) if pattern.bit_count() & 1]


def main():
    from source_chart_cover_portfolio import solve

    table = fixed_dfa()
    records = {}

    def check(label, n, rows, pins, status, route, count, *, exact_twice=False, **opts):
        names, models = oracle(rows, pins)
        assert len(models) == count
        outcome = solve(n, rows, source_pins=pins, exact_twice=exact_twice, **opts)
        assert (outcome['status'], outcome['route']) == (status, route), (label, outcome['attempts'])
        if status == 'SAT':
            true = outcome['true_variables']
            assert true == tuple(sorted(set(true))) and set(true) <= set(names)
            mask = sum(1 << j for j,v in enumerate(names) if v in true)
            assert mask in models
            index = {v:j+1 for j,v in enumerate(names)}
            dense = [tuple(index[abs(l)] if l > 0 else -index[-l] for l in row) for row in rows]
            job = compile_source(len(names), dense, exact_twice=exact_twice)
            raw = outcome['physical']
            assert run_machine(table, raw)[0] == 1
            key = raw_key(raw, job.slots_n)
            assert key >> job.slots_n == 1 and raw == encode([], job.slots_n, key)
            assert run_machine(table, encode([], job.slots_n, key ^ (1 << job.slots_n)))[0] == 0
            lifted = job.lift(raw)
            assert all((mask ^ lifted) & (1 << (abs(l)-1)) == 0 for row in dense for l in row)
        else:
            assert outcome['physical'] is None and outcome['true_variables'] is None
        records[label] = [status, route, count]
        return outcome

    prefix = xor_zero((1,2,3)) + xor_zero((1,2,4))
    for bit, terminal, expected, count in [(0, [(-3,4),(3,-4)], 'SAT',4),
                                            (1, [(3,4),(-3,-4)], 'UNSAT',0)]:
        rows = prefix + terminal
        assert solve_prepass(4,rows) == ('UNKNOWN',None,'non-renamable')
        check('mixed-xor-'+str(bit),4,rows,(),expected,'chart',count, stages=(),node_cap=0)
    n = (1 << 503) + 11
    check('sparse-chart',n,xor_zero((9,67,n)),[(9,0),(67,1),(n-1,1)],'SAT','chart',1,
          exact_twice=True, stages=(),node_cap=0)
    check('contradictory-pins',n,[(9,67,n)],[(n,1),(n,0)],'UNSAT','chart',0,
          stages=(),node_cap=0)
    # A single forbidden corner has codimension three in every invertible chart.
    # Its seven models force a genuine chart abstention before the cover search.
    for cap, expected in [(0,'UNKNOWN'),(8,'SAT')]:
        got=check('fallback-'+str(cap),3,[(-1,2,-3)],(),expected,'cover',7,
                  prepass=False,stages=(),node_cap=cap)
        attempts = got['attempts']
        assert [a['route'] for a in attempts] == ['chart','projected','cover']
        assert attempts[-1]['metrics']['nodes'] == (0 if cap == 0 else 1)
    print(json.dumps(records,sort_keys=True))


if __name__=='__main__':
    main()
