import os
from low_aux import Search,profiles
from pysat.solvers import Cadical195
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess,sys
direct=sys.argv[1]=='direct'
tasks=profiles() if direct else ([p for p in range(32) if C>>p&1] for C in (int(l.split()[0]) for l in Path('faceprofiles.out').read_text().splitlines()))
checker=os.environ.get('DRAT_TRIM','drat-trim')
for i,pts in enumerate(tasks):
    if len(sys.argv)>2 and i<int(sys.argv[2]):continue
    if len(sys.argv)>3 and i>=int(sys.argv[3]):continue
    if not direct and any(len({p>>j&1 for p in pts})<2 for j in range(5)):continue
    m=Search(pts,direct,4,2 if direct else 1)
    with TemporaryDirectory() as tmp:
        base=Path(tmp);f=base/'c.cnf';c=base/'c.drat'
        with f.open('w') as h:
            print('p cnf',m.nv,len(m.cs),file=h)
            for row in m.cs:print(*row,0,file=h)
        with Cadical195(bootstrap_with=m.cs,with_proof=True) as s:
            assert s.solve() is False
            c.write_text('\n'.join(s.get_proof())+'\n')
        o=subprocess.run([checker,str(f),str(c)],capture_output=True,check=True)
        assert b's VERIFIED' in o.stdout
        print(i,sum(1<<p for p in pts),'DRAT verified',flush=True)
