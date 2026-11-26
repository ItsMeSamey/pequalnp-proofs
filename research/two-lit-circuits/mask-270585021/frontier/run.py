from pathlib import Path
import subprocess
cases=[(i,j) for i in range(6) for j in range(i,6)]
raw=270585021
target=sum(((raw>>(6*i+j))&1)<<k for k,(i,j) in enumerate(cases))
def adequate(f):
    seen={}
    for k,(i,j) in enumerate(cases):
        trace=f&((1<<i)|(1<<j))
        bit=target>>k&1
        if seen.setdefault(trace,bit)!=bit:return False
    return True
jobs=[(9-t,t,f) for f in range(1,64) if adequate(f) for t in range(11-f.bit_count())]
jobs.sort(key=lambda k:(k[2],abs(k[1]-2)))
Path('keys.tsv').write_text(''.join(f'{b}\t{t}\t{f}\n' for b,t,f in jobs))
with open('result.log','w') as out:
    for b,t,f in jobs:
        line=subprocess.check_output(['/dev/shm/register21',str(target),str(b),str(t),str(f)],text=True)
        out.write(line);out.flush()
        if ' SAT ' in line:break
