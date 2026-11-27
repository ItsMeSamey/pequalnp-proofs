"""Independent original-source census and minimum interval majority cost."""
from itertools import product
import json
from check_source_cover_portfolio import oracle
from check_event_tree_native import raw_key, run_machine
from padding_cnf import encode
from stage6_source_solver import compile_source, fixed_dfa
from source_nand_compile import compile_source as compile_nand


def minimum(job, supplied):
    n, gates = job['inputs'], job['gates']
    observed = set(job.get('observed',(job['target'],)))
    if not gates:
        assert not supplied
        return 0
    best = {0: 0}
    costs = {}
    for i in range(len(gates)):
        for end in range(i + 1, len(gates) + 1):
            outer = {x for j, pair in enumerate(gates) if j < i or j >= end for x in pair}
            incoming = sorted({x for pair in gates[i:end] for x in pair if x < n + i})
            if len(incoming) > 2:
                break
            ports = [x for x in incoming if x >= n or x in observed or x in outer]
            ports += [x for x in range(n + i, n + end) if x in observed or x in outer]
            traces = set()
            for bits in product(range(2), repeat=len(incoming)):
                values = dict(zip(incoming, bits))
                for j in range(i, end):
                    a,b = gates[j]
                    values[n+j] = 1 ^ (values[a] & values[b])
                traces.add(sum(values[x] << k for k,x in enumerate(ports)))
            c = int(any(((a & b) | (a & c) | (b & c)) not in traces
                        for a,b,c in product(traces,repeat=3)))
            costs[i,end] = c
            best[end] = min(best.get(end, len(gates)+1), best[i]+c)
    path = tuple(map(tuple,supplied))
    assert path[0][0] == 0 and path[-1][-1] == len(gates)
    assert all(a[1] == b[0] for a,b in zip(path,path[1:]))
    assert sum(costs[t] for t in path) == best[len(gates)]
    return best[len(gates)]


def witness(rows, pins, result, twice, count):
    names = sorted({abs(x) for row in rows for x in row} | {v for v,b in pins})
    if result['status'] == 'SAT':
        ids = result['true_variables']
        assert ids == tuple(sorted(set(ids))) and set(ids) <= set(names)
        mask = sum(1 << j for j,v in enumerate(names) if v in ids)
        assert all(any((abs(x) in ids) == (x>0) for x in row) for row in rows)
        assert all((v in ids) == bool(b) for v,b in pins) and count > 0
        idx = {v:j+1 for j,v in enumerate(names)}
        dense = [tuple(idx[abs(x)] if x > 0 else -idx[-x] for x in row) for row in rows]
        job = compile_source(len(names),dense,exact_twice=twice)
        raw = result['physical']
        direct = fixed_dfa()
        assert run_machine(direct,raw)[0] == 1
        key = raw_key(raw,job.slots_n)
        assert key >> job.slots_n == 1 and raw == encode([],job.slots_n,key)
        assert run_machine(direct,encode([],job.slots_n,key ^ (1<<job.slots_n)))[0] == 0
        proj = job.lift(raw)
        assert all((proj ^ mask) & (1<<(abs(x)-1)) == 0 for r in dense for x in r)
    else:
        assert result['physical'] is None and result['true_variables'] is None
        assert result['status'] == 'UNKNOWN' or result['status'] == 'UNSAT' and count == 0
    return count


def ring(h, relaxed):
    groups = []
    for i in range(4*h):
        y = 3 + 3*i
        a, b = (1 if i&1 else -1), (2 if i&2 else -2)
        groups.append([(a,b,y),(-y,y+1),(-y-1,y+2),(-y-2,y if relaxed and i%4==1 else -y)])
    total = 0
    for a,b in product(range(2),repeat=2):
        size = 1
        for i, group in enumerate(groups):
            ways = 0
            for yy,zz,ww in product(range(2),repeat=3):
                vals = {1:a,2:b,3+3*i:yy,4+3*i:zz,5+3*i:ww}
                ways += all(any(vals[abs(x)] == (x>0) for x in row) for row in group)
            size *= ways
        total += size
    return [r for part in groups for r in part],total


def cover_nodes(v):
    from math import prod
    block = max(1,(v+1).bit_length()-1)
    widths = [min(block,v-i) for i in range(0,v,block)]
    def greedy(k):
        balls = [{p for p in range(1<<k) if (p^q).bit_count() <= k//4} for q in range(1<<k)]
        free = set(range(1<<k))
        count = 0
        while free:
            best = max(range(1<<k), key=lambda j:len(balls[j] & free))
            free -= balls[best]
            count += 1
        return count
    return prod(greedy(k) for k in widths)*sum(3**i for i in range(1+sum(k//4 for k in widths)))


def main():
    from source_nand_portfolio import solve as pure
    from source_mixed_nand_portfolio import solve as both
    from source_mixed_nand import compile_source as compile_mixed

    report = {}
    def clocks(m,job):
        b = minimum(job,m['intervals'])
        assert m['bad_blocks'] == b and m['branch_bound'] == 1<<b
        assert m['cover_bound'] == cover_nodes(job['inputs'])
        return b
    for h in (1,2):
        for relaxed in (False,True):
            rows,count = ring(h,relaxed)
            n = 12*h+2
            assert count == (27**h if relaxed else 0)
            if h == 1:
                assert count == len(oracle(rows,())[1])
            expected = 'SAT' if count else 'UNSAT'
            opts = dict(stages=(),node_cap=0)
            got = both(n,rows,nand_branch_cap=2,**opts)
            assert (got['status'],got['route']) == (expected,'mixed-nand'), got['attempts']
            witness(rows,(),got,False,count)
            job = compile_mixed(n,rows)
            met = got['attempts'][0]['metrics']
            assert clocks(met,job) == 1 and met['dispatched']
            assert job['pair_count']==4 and job['not_gates']==2 and len(job['gates'])==6
            assert len(job['clauses'])==16*h and job['pair_frequency_visits']==30*h
            off = both(n,rows,nand_branch_cap=0,**opts)
            assert off['status']=='UNKNOWN' and off['route']=='cover', off['attempts']
            assert off['attempts'][0]['metrics']['dispatched'] is False
            assert any(t['route']=='prepass' and t['status']=='UNKNOWN' for t in off['attempts'])
            assert any(t['route']=='chart' and t['status']=='unknown' for t in off['attempts'])
            witness(rows,(),off,False,count)
            report[f'ring-{h}-{expected}'] = [count,got['route'],met['branch_bound'],off['status'],met['cover_bound']]
            if h == 1:
                # Compare with all three projected kernels at their shipped per-kernel defaults.
                active = ('projected_gaussian','projected_compressed','projected_rank2')
                base = both(n,rows,nand_branch_cap=0,stages=active,node_cap=0)
                assert base['status'] in ('UNKNOWN',expected)
                witness(rows,(),base,False,count)
                report[f'active-{expected}'] = [base['status'],base['route']]
    high = (1<<503)+71
    controls = [
        ('sparse',high,[(high,13,29),(high,high),(13,-13,29)],[(high-2,1)],'SAT','nand'),
        ('negative',3,[(2,),(-2,)],[],'UNSAT','nand'),
        ('repeat',4,[(-4,-4,-4),(2,-2)],[],'SAT','nand'),
        ('empty',0,[],[],'SAT','nand-constant'),
        ('empty-row',0,[()],[],'UNSAT','nand-constant'),
        ('pin-conflict',high,[],[(high,1),(high,0)],'UNSAT','nand-constant')]
    for name,n,rows,pins,status,route in controls:
        count = len(oracle(rows,pins)[1])
        opt = dict(source_pins=pins,exact_twice=True,stages=(),node_cap=0)
        on = pure(n,rows,**opt)
        assert (on['status'],on['route']) == (status,route), (name,on['attempts'])
        witness(rows,pins,on,True,count)
        if route=='nand':
            m = on['attempts'][0]['metrics']
            b = clocks(m,compile_nand(n,rows,pins=pins))
            assert m['dispatched'] and (1<<b)<=m['cover_bound']
            off = pure(n,rows,nand_branch_cap=0,**opt)
            assert off['attempts'][0]['metrics']['dispatched'] is False
            assert off['status']==status
            witness(rows,pins,off,True,count)
        report[name] = [on['status'],count,route]
    print(json.dumps(report,sort_keys=True))


if __name__=='__main__':
    main()
