"""Exhaustive small pair-cover census, independent of selector search."""
from itertools import combinations, product
import json
from check_literal_nand_portfolio import minimum, witness
from check_source_cover_portfolio import oracle


def scopes(rows):
    return sorted({tuple(sorted(map(abs,row))) for row in rows
                   if len({abs(x) for x in row}) == 3})


def optimum(rows):
    triples = scopes(rows)
    pairs = sorted({p for row in triples for p in combinations(row,2)})
    for k in range(len(triples)+1):
        for chosen in combinations(pairs,k):
            if all(any(set(p) <= set(row) for p in chosen) for row in triples):
                return k
    raise AssertionError('no cover')


def greedy(rows):
    live = list(scopes(rows))
    selected = []
    while live:
        pairs = {p for row in live for p in combinations(row,2)}
        choice = min(pairs,key=lambda p:(-sum(set(p)<=set(r) for r in live),p))
        selected.append(choice)
        live = [r for r in live if not set(choice)<=set(r)]
    return selected


def fixture():
    return [(1,2,3),(1,2,4),(1,3,5),(2,4,6)]


def check_pair_solver():
    from source_pair_cover import solve, solve_scopes
    checked = 0
    for family in (fixture(),list(combinations(range(1,5),3))):
        for mask in range(1<<len(family)):
            rows = [r for j,r in enumerate(family) if mask>>j&1]
            opt = optimum(rows)
            for cap in (0,1,None):
                got = solve_scopes(rows,node_cap=cap)
                cov = got['cover']
                assert all(any(set(p)<=set(r) for p in cov) for r in rows)
                assert len(set(cov))==len(cov)==got['upper_bound']
                assert got['lower_bound'] <= opt <= got['upper_bound']
                if got['status']=='optimal':
                    assert got['lower_bound']==opt==len(cov)
                else:
                    assert got['status']=='cutoff' and cap is not None
                if cap is not None:
                    assert got['metrics']['nodes']<=cap
                checked += 1
    rows = fixture()
    assert len(greedy(rows))==3 and optimum(rows)==2
    limited, exact = (solve(6,rows,node_cap=c) for c in (0,None))
    assert limited['status']=='cutoff' and limited['upper_bound']==3
    assert exact['status']=='optimal' and exact['upper_bound']==2
    return checked


def verify_compiled(job):
    for bits in product(range(2),repeat=job['inputs']):
        src = {**job['fixed'],**dict(zip(job['active'],bits))}
        valid = all(any(src.get(abs(x),0)==(x>0) for x in row) for row in job['original'])
        wires = list(bits)
        for a,b in job['gates']:
            wires.append(int(not(wires[a] and wires[b])))
        accepts = all(any(wires[abs(x)-1]==(x>0) for x in row) for row in job['clauses'])
        assert valid == accepts
    for a,b in job['banks']:
        incoming = {w for operands in job['gates'][a:b] for w in operands if w<job['inputs']+a}
        assert len(incoming)==2 and max(incoming)<job['inputs']


def main():
    from source_bank_portfolio import solve
    from source_bank_nand import compile_source
    records = {'cover_queries':check_pair_solver()}
    n = (1<<379)+33
    sparse = [tuple(n if v==6 else v for v in row) for row in fixture()]
    negatives = [tuple(s*v for s,v in zip(signs,(1,2,3))) for signs in product((-1,1),repeat=3)]
    opts = dict(stages=(),prepass=False,node_cap=0,exact_twice=True)
    cases = [
        ('sparse-opt', n,sparse,[(n-1,1)],None,0,4,'SAT'),
        ('greedy',6,fixture(),[],0,0,8,'SAT'),
        ('cap-decline',6,fixture(),[],0,0,4,'UNKNOWN'),
        ('strict-inconsistent',6,fixture()+negatives,[],None,None,4,'UNSAT')]
    for label,arity,rows,pins,pcap,gcap,branches,expect in cases:
        count = len(oracle(rows,pins)[1])
        j = compile_source(arity,rows,pins=pins,pair_node_cap=pcap)
        verify_compiled(j)
        ans = solve(arity,rows,source_pins=pins,pair_node_cap=pcap,partition_gate_cap=gcap,
                    nand_branch_cap=branches,**opts)
        assert ans['status'] == expect, (label,ans['attempts'])
        witness(rows,pins,ans,True,count)
        m = ans['attempts'][0]['metrics']
        assert m['pair_count'] == len(j['banks']) == (3 if pcap==0 else 2)
        assert m['optimizer_used'] == (gcap is None)
        if m['optimizer_used']:
            assert minimum(j,m['intervals'])==m['bad_blocks']
        else:
            assert m['intervals']==j['banks'] and m['bad_blocks']==len(j['banks'])
        if expect=='UNKNOWN':
            assert not m['dispatched'] and ans['route']=='cover' and m['branch_bound']>branches
        else:
            assert ans['route']=='bank-nand' and m['dispatched']
        records[label]=[ans['status'],count,m['pair_search']['status'],m['pair_count'],m['branch_bound']]
    print(json.dumps(records,sort_keys=True))


if __name__=='__main__':
    main()
