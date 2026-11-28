"""Isolate the effect of the default pair search budget on one original CNF."""
import json
from check_literal_nand_portfolio import minimum, witness, cover_nodes
from check_source_cover_portfolio import oracle
from check_unsigned_banks import optimum
from bank_greedy_chart_fixture import chart_gap
from source_bank_nand import compile_source
from source_first_bank_portfolio import solve


def main():
    n,rows = chart_gap()
    models = len(oracle(rows,())[1])
    assert n==9 and models == 28 and optimum(rows)==2
    records = {}
    for mode,extra,expect,b in [('default',{},'SAT',2),('greedy',{'pair_node_cap':0},'UNKNOWN',3)]:
        ans = solve(n,rows,stages=(),node_cap=0,nand_branch_cap=4,**extra)
        assert ans['status']==expect, ans['attempts']
        attempts = ans['attempts']
        assert [r['route'] for r in attempts[:5]]==['chart','prepass','projected','cover','bank-nand']
        assert attempts[0]['status']=='unknown' and attempts[1]['method']=='non-renamable'
        m = attempts[4]['metrics']
        assert m['cover_bound']==cover_nodes(9)==512
        assert m['discovery_cap']==(0 if mode=='greedy' else 512)
        job = compile_source(n,rows,pair_node_cap=m['discovery_cap'])
        assert m['optimizer_used'] and minimum(job,m['intervals']) == m['bad_blocks'] == b
        assert m['pair_count']==b and m['branch_bound']==1<<b
        assert m['dispatched'] == (mode=='default')
        witness(rows,(),ans,False,models)
        records[mode]=[ans['status'],ans['route'],m['discovery_cap'],b,models]
    easy = solve(2,((1,-2),),stages=(),node_cap=0,nand_branch_cap=0)
    assert easy['status']=='SAT' and easy['route']=='chart'
    assert all(a['route']!='bank-nand' for a in easy['attempts'])
    witness(((1,-2),),(),easy,False,3)
    records['easy']=[easy['status'],easy['route']]
    print(json.dumps(records,sort_keys=True))


if __name__=='__main__':
    main()
