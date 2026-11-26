"""Rebuild the nine-input, five-genuine-AND exclusion."""
from pathlib import Path
import subprocess
import tempfile
here=Path(__file__).resolve().parent
def run(c,data=None):
    return subprocess.run(c,input=data,stdout=subprocess.PIPE,check=True).stdout
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    sources={'profile':here/'profile.cpp','quota':here/'quota.cpp','exact':here/'exact.cpp',
             'canon':here.parents[2]/'verification/threshold-nine/canon6.cpp',
             'full':here.parent/'nine-six/full.cpp'}
    for name,file in sources.items():
        run(['c++','-std=c++20','-O3',str(file),'-o',str(d/name)])
    data=run([d/'canon'],run([d/'profile','9','4']))
    rows=data.splitlines();assert len(rows)==738
    quota=[list(map(int,z.split())) for z in run([d/'quota'],data).splitlines()]
    assert [a[0] for a in quota]==list(range(738))
    passing=[i for i,_,ok in quota if ok];assert len(passing)==597
    [full]=[i for i in passing if sorted(map(int,rows[i].split()))==[0]+[2**64-1]*5]
    rest=[i for i in passing if i!=full]
    inputs=b''.join(str(i).encode()+b' '+rows[i]+b'\n' for i in rest)
    refined=[list(map(int,z.split())) for z in run([d/'exact','0','4','0','6'],inputs).splitlines()]
    assert [r[0] for r in refined]==rest and all(not r[1] for r in refined)
    for w,line in zip([4,5],(here/'full.log').read_bytes().splitlines(),strict=True):
        assert run([d/'full','5',str(w),'0','16']).strip()==line and line.endswith(b'SAT 0')
    print('738 profiles, 596 exact non-full exclusions, all-full anchor exclusion')
