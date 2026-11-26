from pathlib import Path
import subprocess
goal=7879121
def fields(f):
    return [sum(1<<k for k in range(25) if (k//5 if i<5 else k%5)==i%5)
            for i in range(10) if f>>i&1]
def separates(f):
    masks=fields(f)
    observed={}
    for k in range(25):
        trace=tuple((m>>k)&1 for m in masks)
        answer=(goal>>k)&1
        if observed.setdefault(trace,answer)!=answer:return False
    return True
def invoke(target,b,t,f):
    return subprocess.check_output(['/dev/shm/register25',str(target),str(b),str(t),str(f)],text=True)
jobs=[(b,t,f) for f in range(1,1024) if separates(f)
      for t in range(10) for b in [9-t] if b>=f.bit_count()-1]
Path('keys.tsv').write_text(''.join(f'{b}\t{t}\t{f}\n' for b,t,f in jobs))
with open('negative.log','w') as out:
    for b,t,f in jobs:
        line=invoke(goal,b,t,f)
        assert ' UNSAT ' in line
        out.write(line);out.flush()
for target,b,name in [(goal^(1<<19),8,'adjacent9.log'),(goal,9,'positive10.log')]:
    out=invoke(target,b,1,825)
    Path(name).write_text(out)
    assert ' SAT ' in out
