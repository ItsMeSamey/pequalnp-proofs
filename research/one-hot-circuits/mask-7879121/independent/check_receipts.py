import re
from pathlib import Path
from weighted import Check,SUP,T,control,keys
here=Path(__file__).parent
control()
rows=[tuple(map(int,s.split()[:4])) for s in (here/'independent.tsv').read_text().splitlines()]
assert len(rows)==len(set(keys()))==len(set(rows))==75
assert set(rows)=={(k,b,n,0) for k,b,n in keys()}
primary=here/'primary.tsv'
if primary.exists():
    pres={tuple(map(int,s.split())) for s in primary.read_text().splitlines()}
    assert set(rows)==pres
def trace(final,ops):
    seen=set(SUP[i] for i in range(8) if 119>>i&1)
    for op,x,y,z in ops:
        assert x in seen and (op=='!' or y in seen)
        assert (65535^x if op=='!' else x&y if op=='&' else x|y)==z
        seen.add(z)
    assert ops[-1][-1]==final
ops=[('|',240,4369,4593),('|',4593,8738,13299),('&',3840,13299,768),('|',15,768,783),('|',4593,17476,22005),('&',783,22005,261),('|',783,22005,22527),('!',22527,0,43008),('|',261,43008,43269)]
trace(43269,ops)
print('75 distinct support/budget keys rejected. Physical baseline passed all 25 cells. Nine-gate neighbor 43269 independently evaluated.')
