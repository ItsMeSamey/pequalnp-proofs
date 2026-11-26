"""Rebuild the nine-input six-AND exclusion from its finite definitions."""
from collections import Counter
from pathlib import Path
import subprocess
import tempfile
here = Path(__file__).resolve().parent
canonical = here.parents[2] / 'verification' / 'threshold-nine'

def run(cmd, data=None):
    return subprocess.run(cmd,input=data,stdout=subprocess.PIPE,check=True).stdout

with tempfile.TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    for name in ['profile6','canon6','quota','low','high','exact','full']:
        source=(canonical if name in ['profile6','canon6'] else here)/(name+'.cpp')
        subprocess.run(['c++','-O3','-std=c++20',str(source),'-o',str(tmp/name)], check=True)
    masks=run([tmp/'canon6'],run([tmp/'profile6','9','4']))
    rows=masks.splitlines()
    assert len(rows)==41798
    quotas=[list(map(int,z.split())) for z in run([tmp/'quota'],masks).splitlines()]
    assert [z[0] for z in quotas]==list(range(len(rows)))
    selected=[rows[i] for i,q,allowed in quotas if allowed]
    assert len(selected)==37860
    data=b'\n'.join(selected)+b'\n'
    search=run([tmp/'low','9','0','1'],data)+run([tmp/'high','9','2','4'],data)
    search=[list(map(int,z.split()[:5])) for z in search.splitlines()]
    assert sorted(r[0] for r in search)==list(range(len(selected)))
    hits={r[0]:r[2] for r in search if r[4]}
    assert Counter(hits.values())==Counter({0:445,1:649,2:168,3:46,4:30})
    full=b'18446744073709551615'
    [all_full]=[i for i in hits if set(selected[i].split())=={full}]
    rest=sorted(set(hits)-{all_full})
    program=b''.join(str(i).encode()+b' '+selected[i]+b'\n' for i in rest)
    refined=[list(map(int,z.split())) for z in run([tmp/'exact','0','4','0','6'],program).splitlines()]
    assert [r[0] for r in refined]==rest and all(r[1]==0 for r in refined)
    for width,line in zip([4,5,6],(here/'full.log').read_bytes().splitlines(),strict=True):
        result=run([tmp/'full','6',str(width),'0','16']).strip()
        assert result==line and result.endswith(b'SAT 0')
    print(f'{len(rows)} canonical profiles, {len(hits)} exact refinements, zero survivors')
