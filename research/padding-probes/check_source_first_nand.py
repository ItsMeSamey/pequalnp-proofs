"""Verify discovery order on a solved source and a genuine chart/prepass miss."""
import json
from check_literal_nand_portfolio import ring, witness
from source_first_nand_portfolio import solve


def main():
    easy = ((2,-5,8),)
    got = solve(8,(r for r in easy),stages=(),node_cap=0,nand_branch_cap=0)
    assert [a['route'] for a in got['attempts']] == ['chart','prepass']
    assert got['status']=='SAT' and got['route']=='prepass'
    witness(easy,(),got,False,7)
    hard, count = ring(1,False)
    assert count==0
    found=solve(14,(r for r in hard),source_pins=iter(()),stages=iter(()),node_cap=0,nand_branch_cap=2)
    visits=[a['route'] for a in found['attempts']]
    assert visits==['chart','prepass','projected','cover','mixed-nand']
    assert found['attempts'][0]['status']=='unknown'
    assert all(t['status']=='UNKNOWN' for t in found['attempts'][1:-1])
    assert found['attempts'][1]['method']=='non-renamable'
    assert found['attempts'][-1]['metrics']['branch_bound']==2
    assert found['status']=='UNSAT' and found['route']=='mixed-nand'
    witness(hard,(),found,False,count)
    print(json.dumps({'easy':['SAT',['chart','prepass']], 'hard':['UNSAT',visits]}))


if __name__=='__main__':
    main()
