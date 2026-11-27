"""MSB quotient regression on original names, forced positions, and lifted interface words."""
import json
from pathlib import Path
import sys
from exact_line import exact_line, pivots, quotient
from line_trace import produce, verify
from generate import extract


def msb(x):
    return x ^ 3 if x & 2 else x


def lsb(x):
    return x ^ 3 if x & 1 else x


def insert_bit(x):
    return (x & 1) | ((x >> 1) << 2)


def check(path):
    assert (msb(1),lsb(1)) == (1,2)
    names=[1,7,11]
    assert [msb(v) for v in names] == [1,4,8]
    assert [lsb(v) for v in names] == [2,4,8]
    original=[3]+[insert_bit(x) ^ (3 if i%2==0 else 0) for i,x in enumerate([2,3,8,10,12,16,18,32])]
    cert=produce(original,names,[0],executable=path)
    assert not verify(original,names,[0],cert) and cert['terminal']=='star'
    assert [len(s['interface']) for s in cert['steps']] == [0,1,2]
    expected=[[],[4],[4,8]]
    assert [s['interface'] for s in cert['steps']] == expected
    oracle_table=pivots([3])
    assert all(quotient(v,oracle_table)==msb(v) for v in [*names,*original])
    residue=[msb(x) for x in original[1:]]
    replay={'columns':residue,'names':[msb(x) for x in names],'forced':[],'certificate':cert}
    values,w,grounds,steps,edges,h,inc,fwd,rev=extract(replay)
    for keep,rows,table in steps:
        assert all(v & 2 == 0 for v in table)
    yes=[3,35,33]
    witness=exact_line(yes,*names,forced=[0])
    assert witness==(0,1,2) and yes[0]^yes[1]^yes[2]==1
    return {'no':{'columns':original,'names':names,'forced':[0],'certificate':cert},
            'quotient':replay,'yes':{'columns':yes,'names':names,'forced':[0],'support':list(witness)}}


if __name__=='__main__':
    rows=check(sys.argv[1])
    Path(sys.argv[2]).write_text(json.dumps(rows,indent=2)+'\n')
    print('MSB 1 versus LSB 2; exact projected names, three split interfaces, forced YES original indices, and physical NO verified.')
