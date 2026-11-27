import contextlib
from fractions import Fraction as F
import io
from pathlib import Path
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    data = runpy.run_path(str(Path(__file__).with_name('repeated_classes.py')))
def score(t):
    r = 25 + sum(t)
    q = 25 + 2*sum(t) + sum(x*x for x in t)
    return F(r*r, 125*q-4*r*r)
def passes(h):
    l = sum(n*score(t) for t,n in h.items())
    d = sum(n*score(t)**2 for t,n in h.items())
    return (17-l)*31*d >= (l-d)**2
print(data['E'], len(data['out']), sum(map(passes,data['out'])))
if data['E'] == 76:
    with contextlib.redirect_stdout(io.StringIO()):
        split = runpy.run_path(str(Path(__file__).with_name('split_margin.py')))
    print('both shores after hubs',sum(passes(h) and passes(g) for h,g in split['left']))
    for h in data['out']:
        if passes(h):
            print(h,split['binary_ok'](h),split['ternary_ok'](h))
