from pathlib import Path
from itertools import combinations
import runpy
c=runpy.run_path(str(Path(__file__).with_name('three-transfer-simplices.py')))
U,full,tests,inv=(c[k] for k in ('universe','full','tests','invertible'))
def factors(e):
    return next(x for x in (e%4,e//4) if x), int(bool(e%4))+2*bool(e//4)
counts={}
for a in combinations(range(16),5):
    s=set(a)
    if not full(s) or not (U-s-set().union(*(q for q in tests if not q&s))):
        continue
    good=0
    for t in s:
        n={t^u for u in s if t!=u and t^u not in inv}
        if len(n)!=2:continue
        x,y=n
        if all(a!=b for a,b in zip(factors(x),factors(y))) and t^x^y not in s:good+=1
    deg=tuple(sorted(sum(y!=x and y^x not in inv for y in s) for x in s))
    counts[deg,good]=counts.get((deg,good),0)+1
assert counts[((2,2,2,3,3),3)]==96
print(counts)
