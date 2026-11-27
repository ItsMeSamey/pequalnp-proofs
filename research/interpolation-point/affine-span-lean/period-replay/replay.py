from pathlib import Path
import sys, hashlib, os, subprocess, json, tempfile, re
dst=Path(__file__).resolve().parent
commit=sys.argv[1]
base='2835d77a9868151d70a102d78273d837823cd169'
rel='research/interpolation-point/affine-span-lean'
w=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='independent-period-'))
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
assert len(allm)==98 and len(new)==12 and sha(src/sys.argv[2])=='72f930c98e7825382c099a7d93e873e519e453745ac27b59c3ec45bc8879fa3c' and sha(src/sys.argv[3])=='e96470882bc0f8732b5e773169306c6aa198da719a02e614c2d2812592bb0535'
for basename, expected, mapped in [('period-full','873281ac41723e17e65d8f73f74ba74d1a27b4ecdf5e6d6f28410c33f7302ef3',allm),('period-increment','2635126dba8af670c589e90031a0fb6ab22277d8717c5b07745a89733ed14889',new)]:
 orig=Path('/dev/shm/exactplane-period')/(basename+'.sha256'); assert sha(orig)==expected and manifest(orig)==mapped
assert set(cache)==set(old) and not old.keys()&new.keys()
assert new.items()<=allm.items() and allm.items()<=(old|new).items()
assert set(allm)-set(new)<=set(old)
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
print('Preflight passed: 90 hashed, 86 imported, 12 queued',flush=True)
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
 build.append(dict(module=n,source_sha256=new[n],olean_sha256=sha(obj),log_sha256=files['.log'],deps=deps));known[n]=obj
 print(n,flush=True)
out=run([str(dst/'controls.lean')]);(dst/'controls.log').write_text(out)
assert out.splitlines()==['(true, false)','(1, true, false)','(false, some 2, false)'],out
audit=w/'Audit.lean';audit.write_text('import ExactPlaneSemanticPeriod\nimport ExactPlaneDirectionalMinors\n#print axioms ExactPlaneCosetDegree.positive\n#print axioms ExactPlaneCosetDegree.period\n#print axioms ExactPlaneDirectionalMinors.positive\n#print axioms ExactPlaneDirectionalMinors.period\n'+''.join('#print axioms ExactPlaneCheckedPeriod.'+key+'\n' for key in ['solve_iff','returned','valid_path','candidate_count','physical_path']))
ax=run([str(audit)]);assert ax.count('[propext, Classical.choice, Quot.sound]')==9
(dst/'receipt.json').write_text(json.dumps(dict(commit=commit,baseline=base,baseline_receipt=sha(receipt_dir/'receipt.json'),new_modules=build,reused={n:[str(o),h] for n,(o,h) in cache.items()},controls=out.splitlines(),axioms=ax.splitlines(),workdir=str(w)),indent=2)+'\n')
