from pathlib import Path
import subprocess
cases=[(i,j) for i in range(5) for j in range(i,5)]
raw=4297
target=sum(((raw>>(5*i+j))&1)<<k for k,(i,j) in enumerate(cases))
def adequate(f):
    seen={}
    for k,(i,j) in enumerate(cases):
        trace=f&((1<<i)|(1<<j))
        bit=target>>k&1
        if seen.setdefault(trace,bit)!=bit:return False
    return True
jobs=[(6-t,t,f) for f in range(1,32) if adequate(f) for t in range(8-f.bit_count())]
jobs.sort(key=lambda k:(k[2],abs(k[1]-2)))
Path('keys.tsv').write_text(''.join(f'{b}\t{t}\t{f}\n' for b,t,f in jobs))
with open('result.log','w') as out:
    for b,t,f in jobs:
        line=subprocess.check_output(['/dev/shm/register15',str(target),str(b),str(t),str(f)],text=True)
        out.write(line);out.flush()
# A fully reachable target on all five sources; two distinct negative cofactors.
control=sum(1<<k for k,(i,j) in enumerate(cases) if i in (1,2) and j in (1,2))
line=subprocess.check_output(['/dev/shm/register15',str(control),'4','1','31'],text=True)
Path('adjacent.log').write_text(line)
assert ' SAT ' in line
for k,(i,j) in enumerate(cases):
    values={sum(1<<u for u,p in enumerate(cases) if a in p):a in (i,j) for a in range(5)}
    for gate in line.splitlines()[1:]:
        a,op,b,_,y=gate.split()
        v=values[int(a)]
        v=(not v) if op=='!' else (v and values[int(b)]) if op=='&' else (v or values[int(b)])
        assert v==bool(int(y)>>k&1)
        values[int(y)]=v
    assert values[control]==(i in (1,2) and j in (1,2))
