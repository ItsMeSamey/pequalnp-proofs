from pathlib import Path
import subprocess,sys
from relations import ps,ns
base=Path(__file__).parent
for script,k in [('abstract.py',3),('k4.py',4)]:
 subprocess.run([sys.executable,str(base/script),str(k),'12'],check=True)
gates=[(8,256),(16,256),(32,4096),(256,4096),(2,4096)]
fixed=[1,4,64,128,512,1024,2048]
out=fixed+[a|b for a,b in gates]
assert len(out)==12
def project(r):return (r>>13&127)|sum(bool((r&8191)&m)<<(i+7) for i,m in enumerate(out))
assert all(project(p)&~project(n) for p in ps for n in ns)
print('5 raw OR gates suffice: all 12 signals plus the seven lines distinguish every original positive from every negative.')
