"""Run in a fresh temporary directory. --check-only verifies the manifest and ledger joins."""
from pathlib import Path
import sys,gzip,hashlib,subprocess,tempfile,os
base=Path(__file__).resolve().parent
for l in (base/'SHA256SUMS').read_text().splitlines():
 h,f=l.split(None,1);assert hashlib.sha256((base/f.strip()).read_bytes()).hexdigest()==h,f
def log(n):return gzip.decompress((base/'logs'/(n+'.gz')).read_bytes())
def rows(n):return [l.split() for l in log(n).decode().splitlines()]
p=rows('outer6-prior.tsv');assert [int(r[0]) for r in p]==list(range(41719))
d={n:rows(f'outer6-direct-{n}.tsv') for n in (4,5,6)};d[6]+=rows('outer6-direct-6b.tsv')
for a in d.values():assert [int(r[0]) for r in a]==list(range(41719))
ids={}
for n,groups in [(4,[('d4-small',0,2048),('d4-step0',2048,10000),('d4-step1',10000,50000),('d4-step2',50000,10**12)]),(5,[('d5-small',0,100000),('d5-med',100000,400000),('d5-big',400000,10**12)])]:
 for key,lo,hi in groups:ids[key]=[int(i) for i,_,v in d[n] if lo<int(v)<=hi and(n==4 or int(p[int(i)][2])<2)]
ids['d5-W2']=[int(i) for i,_,v in d[5] if int(v) and int(p[int(i)][2])==2]
for k in ids:
 out='outer6-'+k+('-complete' if k=='d5-W2' else '')+'.log';assert [int(r[0]) for r in rows(out)]==ids[k]
for w in (1,2):ids[f'd6-W{w}']=[int(i) for i,_,v in d[6] if int(v) and int(p[int(i)][2])==w]
assert [int(r[0]) for r in rows('outer6-z2.tsv')]==ids['d6-W2']
assert [int(r[1]) for r in rows('outer6-z1.tsv') if r[0]=='profile']==ids['d6-W1']
ids['final']=ids['d5-med']+ids['d5-big'];assert len(ids['final'])==12
assert [int(r[1]) for r in rows('outer6-d5-zany.tsv') if r[0]=='profile']==sorted(ids['final'])
last=rows('outer6-d5-joint-pilot.log')+rows('outer6-d5-joint-suffix.log')
assert [int(r[1]) for r in last]==[i for i in sorted(ids['final']) if i!=41718]
assert sum(int(r[5]) for r in last)==1536 and all(int(r[7])==int(r[9])==0 for r in last)
print('manifest and cross-ledger coverage verified',flush=True)
if '--check-only' in sys.argv:raise SystemExit
tmpdir=tempfile.TemporaryDirectory();tmp=Path(tmpdir.name);os.chdir(tmp)
Path('six').write_bytes(gzip.decompress((base/'six-all.txt.gz').read_bytes()))
for k,v in ids.items():Path(k+'.ids').write_text(''.join(f'{i}\n' for i in v))
Path('control.ids').write_text('0\n')
def compile(src,exe):subprocess.run([os.environ.get('CXX','c++'),'-std=c++20','-O3',str(src),'-o',str(exe)],check=True)
for src in base.glob('outer*.cpp'):compile(src,tmp/src.stem)
def run(exe,argv,stdin,expected):
 with Path(stdin).open('rb') as f:out=subprocess.check_output([str(tmp/exe),*map(str,argv)],stdin=f)
 assert out==log(expected),expected
 Path(expected).write_bytes(out);print(expected,flush=True)
for k,out in [('outer5direct','outer5direct.tsv'),('outer5d4','outer5d4.log'),('outer5d5','outer5d5.log')]:run(k,[],base/'canonfive.out',out)
subprocess.run(['python3',str(base/'outer5-controls.py'),str(tmp/'controls')],cwd=base,check=True)
tail=(base/'canonfive.out').read_bytes().splitlines()[-1]+b'\n'
for n in (4,5):
 compile(tmp/'controls'/f'outer5d{n}.cpp',tmp/'control5');assert b'extensions 1' in subprocess.check_output([tmp/'control5'],input=tail)
subprocess.run([tmp/'outer6-interpolation-control'],check=True)
run('outer6-prior',[],'six','outer6-prior.tsv')
for n,lo,hi,s in [(4,0,41719,'4'),(5,0,41719,'5'),(6,0,29369,'6'),(6,29369,41719,'6b')]:run('outer6-direct',[n,lo,hi],'six',f'outer6-direct-{s}.tsv')
run('outer6-z2',[6,0,41719,'d6-W2.ids'],'six','outer6-z2.tsv')
run('outer6-zany',['d6-W1.ids'],'six','outer6-z1.tsv')
run('outer6-zany',['control.ids'],base/'outer6-matching3.control','outer6-control.log')
for k in ['d4-small','d4-step0','d4-step1','d4-step2','d5-small','d5-med','d5-big','d5-W2']:
 n=int(k[1]);fixed=k=='d5-W2';exe='outer6d4' if n==4 else 'outer6d5fixed' if fixed else 'outer6d5relax'
 run(exe,[n,0,41719,k+'.ids'],'six','outer6-'+k+('-complete' if fixed else '')+'.log')
run('outer6-d5-zany',['final.ids'],'six','outer6-d5-zany.tsv')
for lo,hi,s in [(0,32360,'pilot'),(32360,41719,'suffix')]:run('outer6-d5-joint',['outer6-d5-zany.tsv',lo,hi],'six',f'outer6-d5-joint-{s}.log')
