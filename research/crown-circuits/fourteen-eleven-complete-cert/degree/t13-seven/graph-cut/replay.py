"""Rebuild, proof-check and apply the initial 26 free-AND graph obstructions."""
import hashlib,os,subprocess,sys,tempfile
from collections import Counter
from pathlib import Path
from cert import check
here=Path(__file__).resolve().parent
drat=str(Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as tmp:
 os.chdir(tmp);negative={}
 for row in (here/'initial-drat.tsv').read_text().splitlines():
  p,g,r,digest,_=row.split();p,g,r=map(int,[p,g,r])
  assert not check(p,g,r)
  cnf,proof=[Path(f'cert-{p}-{g}.'+ext) for ext in ['cnf','drat']]
  assert hashlib.sha256(cnf.read_bytes()).hexdigest()==digest
  answer=subprocess.run([drat,cnf,proof],capture_output=True,check=True)
  assert b's VERIFIED' in answer.stdout
  negative[p,g]=max(r,negative.get((p,g),-1));cnf.unlink();proof.unlink()
 for name in ['colored','induced']:
  subprocess.run(['c++','-std=c++20','-O3',here.parent/(name+'.cpp'),'-o',name],check=True)
 with open('models','wb') as models:
  for p in range(3,8):
   subprocess.run(['./colored','7',str(p)],stdout=subprocess.DEVNULL,stderr=models,check=True)
 with open('models','rb') as models,open('refs','wb') as refs,open('queries','wb') as queries:
  subprocess.run(['./induced'],stdin=models,stdout=refs,stderr=queries,check=True)
 rejected=set()
 for line in Path('queries').read_text().splitlines():
  i,p,g,r=map(int,line.split())
  if r<=negative.get((p,g),-1):rejected.add(i)
 total=Counter();fail=Counter()
 for row,refs in zip(Path('models').read_text().splitlines(),Path('refs').read_text().splitlines(),strict=True):
  p,g,u,b=map(int,row.split());key=p,u.bit_count()+b.bit_count(),b.bit_count()
  total[key]+=1;fail[key]+=not rejected.isdisjoint(map(int,refs.split()[1:]))
 assert (sum(total.values()),sum(fail.values()))==(26634,10711)
 assert {k for k in total if total[k]==fail[k]}=={(6,4,0),(6,1,1),(7,6,2),(7,5,1)}
 print('26 DRAT-verified obstructions, 10711/26634 colored models excluded')
