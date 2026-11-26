from pathlib import Path
import subprocess
import sys
import tempfile
from repair import run
here=Path(__file__).resolve().parent
source=Path(sys.argv[1]).resolve()
expected={
 '012': (12,593,176109,12), '014': (12,590,172966,12),
 '015': (6,1104,608935,5), '046': (1,590,172935,3), '123': (4,593,176037,12)}
with tempfile.TemporaryDirectory() as td:
    work=Path(td)
    subprocess.run([sys.executable,here/'inputs.py',source,work],check=True)
    report=subprocess.check_output([sys.executable,here/'orbits.py',source],text=True).splitlines()
    assert report[0]=='24 5' and {z.split()[0]:int(z.split()[1]) for z in report[1:]}=={k:v[0] for k,v in expected.items()}
    subprocess.run(['c++','-std=c++17','-O3',here/'evaluate.cpp','-o',work/'evaluate'],check=True)
    for tri,(orbit,n4,n5,hard) in expected.items():
        for b,n in [(4,n4),(5,n5)]:
            case=work/tri;remaining=work/'remaining'
            fields=subprocess.check_output([work/'evaluate',case,str(b),remaining],text=True).split()
            hist=list(map(int,fields[3:]))
            assert int(fields[2])==n==sum(hist)
            assert sum(hist[b+1:])==(0 if b==4 else hard)
            if b==4:assert not sum(hist[4:])
            else:run(case,remaining)
            print(tri,orbit,b,n,hist,flush=True)
