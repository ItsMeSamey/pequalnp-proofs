"""Verify every archived search ID, positive control and seven-AND stratum."""
from pathlib import Path
import subprocess as sp
import sys
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root/'seven'))
from verify_higher import verify
def rows(f):return [list(map(int,r.split())) for r in f.read_text().splitlines() if r.strip()]
sp.run([sys.executable,str(root/'control.py')],check=True)
seven=root/'seven'; low=root/'low-dirty'
for w in range(4,8):
    tokens=(low/f'clean-seven-{w}.log').read_text().split()
    assert tokens[:8]==['axes','7','weight',str(w),'singleton','0','budget','17'] and tokens[-2:]==['SAT','0']
for i,points in enumerate([96,112,120,124,126,127]):
    [r]=rows(low/f'one-dirty-{i}.log')
    assert r[:3]==[i,points,5 if i==0 else 4] and r[3]>0 and r[4]==0
catalog=rows(seven/'physical-two-catalog.tsv')
assert len(catalog)==68 and [r[0] for r in catalog]==list(range(68))
for cost,expected in enumerate([4,9,21,34]):
    result=rows(seven/f'cost-{cost}.tsv');required={r[0] for r in catalog if r[1]==cost}
    assert len(required)==len(result)==expected and {r[0] for r in result}==required
    assert all(len(r)==8 and r[1]==cost and r[-1]==0 for r in result)
print('Verified four all-clean widths, six one-dirty classes, 68 two-dirty templates.',flush=True)
d=3
verify(d,seven/'catalog-3.tsv',seven/'projection-3.tsv',seven/'cycles-3.tsv',seven/'two-tags-3.tsv',
       [seven/f'residual-3-{c}.tsv' for c in range(3)])
for d in (4,5):
    p=seven/f'higher-{d}'
    verify(d,p/f'higher-{d}.tsv.gz',p/f'projection-{d}.tsv.gz',p/f'cycles-{d}.tsv.gz',p/f'two-tags-{d}.tsv.gz',
           [p/f'early-{d}-0.tsv.gz',p/(f'parallel-{d}-1.tsv.gz' if d==4 else f'early-{d}-1.tsv.gz'),p/f'parallel-{d}-2.tsv.gz'])
p=seven/'six'
verify(6,p/'catalog.tsv.gz',p/'projection.tsv.gz',p/'cycles-6.tsv',p/'two-tags-6.tsv',
       [p/f'parallel-6-{c}.tsv' for c in range(3)])
