import sys,json
from pathlib import Path

from verify_mixed import coords,front,target,sets
data=[coords(j) for j in range(676)]
can=[sum(1<<((6+j+d)%13) for d in [0,1,3,9]) for j in range(7)]
raw={(a,b) for p,(a,l) in enumerate(data) if (target^front)>>p&1 for n,(b,k) in enumerate(data) if not(target>>n&1) and not l&~k}
rel=sorted((a,b) for a,b in raw if not any(a==c and b!=d and not b&~d for c,d in raw))
initial=[(data[p][0],data[n][0]) for p,n in sets['point']]+[(0,0)]
import io, subprocess, tempfile
from collections import Counter
base=Path(__file__).resolve().parent
f=io.StringIO()
assert len(rel)==1323
print(len(rel),file=f)
for a,b in rel+initial:print(a,b,file=f)
print(*can,file=f)

assert len(rel)==1323
with tempfile.TemporaryDirectory() as tmp:
    exe=Path(tmp)/'finite'
    subprocess.run(['c++','-std=c++20','-O2',str(base/'finite.cpp'),'-o',str(exe)],check=True)
    result=subprocess.run([str(exe)],input=f.getvalue(),text=True,capture_output=True,check=True)
def parse(lines):
    return [tuple(map(int,row.split())) for row in lines.splitlines()]
families=parse(result.stdout)
assert families==parse((base/'families.txt').read_text())
assert len(families)==len(set(families))==202
types=Counter()
for family in families:
    assert len(set(family))==8
    assert all(any(a&m and not b&m for m in family) for a,b in rel)
    removed=set(can)-set(family)
    added=set(family)-set(can)
    if len(removed)==1:
        m,=removed
        a,b=added
        assert (a|b)==m
        types[tuple(sorted([a.bit_count(),b.bit_count()]))]+=1
    else:
        assert any(s.bit_count()==1 and all(m&s and (m^s) in added for m in removed) for s in added)
        types[len(removed)]+=1
assert types=={(1,3):28,(2,2):21,(2,3):84,(3,3):42,2:21,3:6}
print('Verified all 202 unordered eight-point families:',types)
