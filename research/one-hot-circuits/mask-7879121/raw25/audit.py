from pathlib import Path
import json
goal=7879121
raw=[sum(1<<k for k in range(25) if (k//5 if i<5 else k%5)==i%5) for i in range(10)]
full=(1<<25)-1
signals=raw[:]
for op,*args in json.loads(Path('control10.json').read_text()):
    x=signals[args[0]]
    y=signals[args[-1]]
    signals.append(x|y if op=='or' else x&y if op=='and' else x^full)
assert len(signals)==20 and signals[-1]==goal
def allowed(f):
    for i in range(25):
        for j in range(i):
            if ((goal>>i)^(goal>>j))&1 and not any(f>>a&1 and ((x>>i)^(x>>j))&1 for a,x in enumerate(raw)):return False
    return True
expected={(9-t,t,f) for f in range(1024) if allowed(f) for t in range(11-f.bit_count())}
actual=[]
for line in Path('negative.log').read_text().splitlines():
    mask,b,t,f,result,*counts=line.split()
    assert int(mask)==goal and result=='UNSAT'
    actual.append(tuple(map(int,(b,t,f))))
assert len(actual)==len(set(actual)) and set(actual)==expected
print(len(actual),'independent raw support/budget keys; 25 cells of the supplied ten-gate control agree.')
