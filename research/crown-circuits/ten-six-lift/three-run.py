from pathlib import Path
import subprocess,sys
p=Path(__file__).parent
cost,start,amount=map(int,sys.argv[1:4])
rows=[x.split()[:3] for x in (p/'t8-three-mandatory.tsv').read_text().splitlines() if int(x.split()[-1])==cost]
with (p/f'three-exact-{cost}-{start:05}.log').open('w') as log:
 for index,t in enumerate(rows[start:start+amount],start):
  r=subprocess.run(['/dev/shm/t8-duality-dirty-exact',*t],capture_output=True,check=True,text=True)
  log.write(r.stdout);log.flush()
  if 'hit 1' in r.stdout:
   ans=subprocess.check_output([sys.executable,str(p/'lift-dirty.py'),*t,*r.stdout.splitlines()[0].split()],text=True)
   (p/'positive-three.json').write_text(ans);print('T8 positive',*t,index);sys.exit(8)
print('complete',cost,start,min(len(rows)-start,amount))
