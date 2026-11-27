from pathlib import Path
import sys, hashlib, os, subprocess, json, tempfile, re
dst=Path(__file__).resolve().parent
commit=sys.argv[1]
base='2835d77a9868151d70a102d78273d837823cd169'
rel='research/interpolation-point/affine-span-lean'
w=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='independent-charges-'))
src=w/rel
fresh=w/'fresh';fresh.mkdir()
receipt_dir=dst.parent/'review-plane-profile'
profile=json.loads((receipt_dir/'receipt.json').read_text()); priorwork=Path((receipt_dir/'workdir').read_text().strip())
cache={n:(Path(v[0]),v[1]) for n,v in profile['reused'].items()}
assert hashlib.sha256((receipt_dir/'receipt.json').read_bytes()).hexdigest()=='92cd60a826711cc63a242e53ceb6c7d4d5204141abce5d488c6e3fbad79e8836'
cache.update({r['module']:(priorwork/'fresh'/(r['module']+'.olean'),r['olean_sha256']) for r in profile['new_modules']})
assert len(cache)==90 and profile['commit']==base
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def manifest(path): return {Path(p).stem:h for h,p in (l.split() for l in path.read_text().splitlines())}
git=['git','-C','/workspace/pnp-research']
sp=subprocess.Popen([*git,'archive',commit,rel],stdout=subprocess.PIPE)
subprocess.run(['tar','x','-C',w],stdin=sp.stdout,check=True); assert sp.wait()==0
allm=manifest(src/sys.argv[2]); new=manifest(src/sys.argv[3]); old=manifest(src/'PROFILE-SOURCES.sha256')
period_dir=dst.parent/'review-plane-coset'
period=json.loads((period_dir/'receipt.json').read_text())
assert sha(period_dir/'receipt.json')=='6f0e9a4d6014b960493de53631f2203bdddda65549ebd5a1d39e9e9be7d437d0'
for m in period['new_modules']:
 cache[m['module']]=(Path(period['workdir'])/'fresh'/(m['module']+'.olean'),m['olean_sha256'])
old.update(manifest(src/'PERIOD-INCREMENT.sha256'))
field_dir=dst.parent/'review-plane-field'
field=json.loads((field_dir/'receipt.json').read_text())
for m in field['new_modules']:
 n=m['module']
 if n not in cache:
  cache[n]=(Path((field_dir/'workdir').read_text().strip())/'fresh'/(n+'.olean'),m['olean_sha256'])
  old[n]=m['source_sha256']
assert sha(src/sys.argv[2])=='4ab1db343b5946fdc0f5e4799089d7b90672feb9279e55e6aad07911d968e19f'
assert sha(src/sys.argv[3])=='72784a31a5739e1a619b06ede1213d2958d787464f7d8a15049d811ee64927c0'
assert not new.keys()&old.keys() and new.items()<=allm.items() and allm.items()<=(old|new).items()
prior=w/'prior';prior.mkdir()
for n,(obj,h) in cache.items():
 assert sha(obj)==h and sha(src/(n+'.lean'))==old[n]
 if n in allm: (prior/obj.name).symlink_to(obj)
for n,h in new.items():assert sha(src/(n+'.lean'))==h
depsdir=Path((dst.parent/'review-plane-raw/workdir').read_text().strip())/'prerequisites'
for file in ['prerequisites.json','reused-prerequisites.json']:
 for entry in json.loads((dst.parent/'review-plane-raw'/file).read_text()):
  assert sha(Path(entry['path']))==entry['olean_sha256']
lib=Path('/workspace/pequalnp-proofs/lean/.lake/packages'); lean='/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'
env={k:v for k,v in os.environ.items() if not k.startswith(('LAKE','LEAN'))}
env['LEAN_PATH']=os.pathsep.join(map(str,[fresh,prior,depsdir,*sorted(lib.glob('*/.lake/build/lib/lean'))]))
def run(args):
 r=subprocess.run([lean,'-j1','--root',str(src),*args],cwd=src,env=env,capture_output=True,text=True)
 if r.returncode: raise RuntimeError(r.stdout+r.stderr)
 return r.stdout+r.stderr
known={n:obj for n,(obj,h) in cache.items() if n in allm};build=[]
(dst/'workdir').write_text(str(w)+'\n')
print('Preflight',len(cache),'prior objects checked;',len(allm)-len(new),'imported;',len(new),'fresh',flush=True)
import time
while not (dst/'compiler-go').exists():time.sleep(1)
while new.keys()-known.keys():
 n=next(n for n in new if n not in known and set(re.findall(r'^import (ExactPlane\w+)',(src/(n+'.lean')).read_text(),re.M))<=known.keys())
 f=n+'.lean';obj=fresh/(n+'.olean')
 deps=run(['--deps',f]).splitlines()
 for line in deps:
  p=Path(line); assert p.exists()
  if p.name.startswith('ExactPlane'):assert known[p.stem].resolve()==p.resolve()
 log=run(['-o',str(obj),f]);(dst/(n+'.log')).write_text(log)
 assert 'sorryAx' not in log
 prod=next((src/d/(n+'.sha256') for d in ('producer','period-producer') if (src/d/(n+'.sha256')).exists()),None)
 if prod is None:prod=next(src.rglob(n+'.sha256'))
 files={Path(p).suffix:h for h,p in (l.split() for l in prod.read_text().splitlines())}
 assert files['.olean']==sha(obj) and files['.lean']==new[n]
 assert files['.log']==sha(dst/(n+'.log'))
 if n=='ExactPlanePivotCount':
  previous=json.loads((dst.parent/'review-plane-gaussian/receipt.json').read_text())
  assert any(r['module']==n and r['olean_sha256']==sha(obj) for r in previous['new_modules'])
 build.append(dict(module=n,source_sha256=new[n],olean_sha256=sha(obj),log_sha256=files['.log'],deps=deps));known[n]=obj
 print(n,flush=True)
out=run([str(dst/'controls.lean')]);(dst/'controls.log').write_text(out)
ax=run([str(dst/'axioms.lean')]);(dst/'axioms.log').write_text(ax)
lines=[l for l in ax.splitlines() if 'depends on axioms' in l]
allowed={'propext','Classical.choice','Quot.sound'}
assert lines and all(set(l.split('axioms: [')[1].strip(']').split(', '))<=allowed for l in lines)
assert len(allm)==86 and len(new)==16
for label,digest,expected in [('full','09dad5e5a09370f92e938caff099499f2523c8ce646d656a4f0e18741b9210aa',allm),('increment','e4791a170ad6e7d271a0a147b283e016bdaa37ce10ac9ce4d7f26d406a22323d',new)]:
 f=Path('/dev/shm/exactplane-charged')/('charged-'+label+'.sha256');assert sha(f)==digest and manifest(f)==expected
(dst/'receipt.json').write_text(json.dumps(dict(commit=commit,baseline=base,period_receipt=sha(period_dir/'receipt.json'),baseline_receipt=sha(receipt_dir/'receipt.json'),new_modules=build,closure=allm,reused={n:[str(o),h] for n,(o,h) in cache.items() if n in allm},controls=out.splitlines(),axioms=lines,workdir=str(w)),indent=2)+'\n')
