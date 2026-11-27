from pathlib import Path
import subprocess
import sys
exe = str(Path(sys.argv[1]).resolve())
cases=[(i,j) for i in range(6) for j in range(i,6)]
raw=270549407
target=sum(((raw>>(6*i+j))&1)<<k for k,(i,j) in enumerate(cases))
def adequate(f):
    seen={}
    for k,(i,j) in enumerate(cases):
        trace=f&((1<<i)|(1<<j))
        bit=target>>k&1
        if seen.setdefault(trace,bit)!=bit:return False
    return True
jobs=[(6-t,t,f) for f in range(1,64) if adequate(f) for t in range(8-f.bit_count())]
jobs.sort(key=lambda k:(k[2],abs(k[1]-2)))
Path('keys.tsv').write_text(''.join(f'{b}\t{t}\t{f}\n' for b,t,f in jobs))
with open('result.log','w') as out:
    for b,t,f in jobs:
        line=subprocess.check_output([exe,str(target),str(b),str(t),str(f)],text=True)
        out.write(line);out.flush()
