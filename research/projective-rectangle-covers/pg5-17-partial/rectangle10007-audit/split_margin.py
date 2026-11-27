"""E=76 extra necessary tests; no geometric completion is claimed."""
from contextlib import redirect_stdout
from functools import lru_cache
from io import StringIO
from math import comb
from pathlib import Path
import runpy
import sys

base=Path(__file__).resolve().parent
sys.argv=['repeated_classes.py','76']
with redirect_stdout(StringIO()):
    old=runpy.run_path(str(base/'repeated_classes.py'))['out']

def binary_ok(h):
    r=sum(count for row,count in h.items() if any(v%2 for v in row))
    p=sum(count for row,count in h.items() if sum(v%2 for v in row)==1)
    d=r-14
    for singles in range(p+1):
        for doubles in range((p-singles)//2+1):
            rem=p-singles-2*doubles
            if rem%3:continue
            repeat=doubles+rem//3
            distinct=singles+repeat
            if repeat>d+1 or distinct>2**d-1:continue
            if 3*repeat<r and repeat:
                if repeat>d:continue
                if p>3*repeat+3*(2**(d-repeat+1)-1-int(r-3*repeat>7)):continue
            if singles*(r-7)+repeat*(r-3)>(2**(d-1) if d else 0)*r:continue
            if r>=18 and distinct*(2*distinct-2**d)>(6 if r<=19 else 0):continue
            return True
    return False

def ternary_ok(h):
    r=sum(count for row,count in h.items() if any(v%3 for v in row))
    one=sum(count for row,count in h.items() if [v%3 for v in row if v%3]==[1])
    two=sum(count for row,count in h.items() if [v%3 for v in row if v%3]==[2])
    return not one or r<15 or two+min(3,(one+2)//3)<=(r-14)*(r-13)//2

def entries(h):
    return sorted(v for row,n in h.items() for v in row for _ in range(n))

def repeats(h):
    return sum(n*(sum(comb(v+1,2) for v in row)-max((comb(v+1,2) for v in row),default=0))
               for row,n in h.items())

shapes=[tuple(map(int,line.split()))[:2] for line in (base/'spectrum.txt').read_text().splitlines()[:-1]]
@lru_cache(None)
def best_area(m,budget):
    if not m:return 0
    return max([a*b+best_area(m-1,budget-(a+b-2)) for a,b in shapes if a+b-2<=budget]+[-10000])

def hub_check(h,g):
    for v in set(entries(h)):
        def extras(x):
            return sorted(sum(row)-v for row,n in x.items() for u in row if u==v for _ in range(n))
        # Match opposite-sorted side costs to maximize the smallest pair sum.
        for a,b in zip(extras(h),reversed(extras(g))):
            if best_area(v+1,48+a+b)+60*(16-v)<851:return False
    return True

aftertriad=[h for h in old if binary_ok(h)]
afterquadratic=[h for h in aftertriad if ternary_ok(h)]
paired=[]
for h in afterquadratic:
    for g in afterquadratic:
        entry=entries(h)
        if entry!=entries(g):continue
        if sum(comb(v+1,2) for v in entry)>136+repeats(h)+repeats(g):continue
        paired.append((h,g))
left=[(h,g) for h,g in paired if hub_check(h,g)]
print('old, triad, ternary, compatible ordered pairs, after hubs:',len(old),len(aftertriad),len(afterquadratic),len(paired),len(left))
assert (len(old),len(aftertriad),len(afterquadratic),len(paired),len(left))==(75,44,31,26,18)
