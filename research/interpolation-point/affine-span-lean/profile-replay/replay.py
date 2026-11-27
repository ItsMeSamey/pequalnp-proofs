from pathlib import Path
import subprocess as sp,hashlib,json,tempfile,os,re
D=Path(__file__).resolve().parent
C='2835d77a9868151d70a102d78273d837823cd169'; rel='research/interpolation-point/affine-span-lean'
resume=os.environ.get('PROFILE_AUDIT_RESUME')=='1'; W=Path((D/'workdir').read_text().strip()) if resume else Path(tempfile.mkdtemp(prefix='review-profile-',dir='/dev/shm')); S=W/rel; O=W/'fresh'; O.mkdir(exist_ok=resume); prior=W/'verified';prior.mkdir(exist_ok=resume)
(D/'workdir').write_text(str(W)+'\n')
p=sp.Popen(['git','-C','/workspace/pnp-research','archive',C,rel],stdout=sp.PIPE);sp.run(['tar','-x','-C',W],stdin=p.stdout,check=True);assert p.wait()==0
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def parse(f):return {Path(b).stem:a for a,b in (l.split() for l in f.read_text().splitlines())}
def lock(f,h): assert sha(f)==h,(f,sha(f),h)
prod=Path('/dev/shm/exactplane-profile')
for name,h in [('profile-full','e126cceb7a22dadc89b8816bab42de4f768d1f760fad9cf8a07c7a827addf5e4'),('profile-increment','cb898d15f397e830ecc01357cbdf9c1ef19529434278cba1db30710afa2c318d')]:lock(prod/(name+'.sha256'),h)
for name,h in [('PROFILE-SOURCES','f5a5ee94faebcf9a1e4d021e18f5773fa2e9ccc15b8b8a2d24bfd8f14382c375'),('PROFILE-INCREMENT','3d3ac0927440962b21fe675f7b129776f46dad2947f5ffcd9e9f30ce4cc60203')]:lock(S/(name+'.sha256'),h)
full=parse(S/'PROFILE-SOURCES.sha256'); inc=parse(S/'PROFILE-INCREMENT.sha256')
assert full==parse(prod/'profile-full.sha256') and inc==parse(prod/'profile-increment.sha256') and (len(full),len(inc))==(90,22)
for n,h in full.items():lock(S/(n+'.lean'),h)
lookup={}; baselines={};reused={}
for q in ('field','gaussian','executable','raw-small','raw','sampler','determinant'):
 folder=D.parent/('review-plane-'+q); file=folder/'receipt.json'; rr=json.loads(file.read_text());baselines[q]=sha(file); fresh=Path((folder/'workdir').read_text().strip())/'fresh'
 for m in rr.get('new_modules',rr.get('modules',[])):
  n=m['module']
  if n in full and n not in inc and n not in lookup:
   assert m['source_sha256']==full[n]; obj=fresh/(n+'.olean');lock(obj,m['olean_sha256'])
   dest=prior/obj.name; 
   if not resume:dest.symlink_to(obj)
   assert dest.resolve()==obj.resolve();lookup[n]=dest;reused[n]=[str(obj),m['olean_sha256'],q]
assert len(lookup)==68
raw=D.parent/'review-plane-raw';extra=Path((raw/'workdir').read_text().strip())/'prerequisites'
for file in ['prerequisites.json','reused-prerequisites.json']:
 for m in json.loads((raw/file).read_text()): lock(Path(m['path']),m['olean_sha256'])
lib=Path('/workspace/pequalnp-proofs/lean/.lake/packages')
lean='/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'
env={k:v for k,v in os.environ.items() if not k.startswith(('LAKE','LEAN'))}
env['LEAN_PATH']=os.pathsep.join(map(str,[O,prior,extra,*sorted(lib.glob('*/.lake/build/lib/lean'))]))
def run(cmd):return sp.check_output(cmd,env=env,cwd=S,text=True,stderr=sp.STDOUT)
new=[]
while set(full)-lookup.keys():
 n=next(n for n in inc if n not in lookup and set(re.findall(r'^import (ExactPlane\w+)',(S/(n+'.lean')).read_text(),re.M))<=lookup.keys())
 f=S/(n+'.lean'); o=O/(n+'.olean'); cmd=[lean,'-j1','--root',S]
 deps=run(cmd+['--deps',f.name]).splitlines()
 for dd in map(Path,deps):
  assert dd.is_file()
  if dd.name.startswith('ExactPlane'):assert dd.resolve()==lookup[dd.stem].resolve()
 log=(D/(n+'.log')).read_text() if resume and o.is_file() and (D/(n+'.log')).is_file() else run(cmd+['-o',o,f.name]);(D/(n+'.log')).write_text(log)
 expected=(S/'producer'/(n+'.log')).read_text()
 ax=lambda x:[l for l in x.splitlines() if 'depends on axioms:' in l]
 assert ax(log)==ax(expected) and 'sorryAx' not in log
 lock((S/'producer'/(n+'.sha256')),sha(prod/(n+'.sha256')))
 for line in (prod/(n+'.sha256')).read_text().splitlines():
  h0,where=line.split();target=Path(where);lock(target,h0)
  if target.suffix=='.olean':assert sha(o)==h0,(n,'independent object differs from producer')
 if 'Examples' in n:assert log==expected
 new.append(dict(module=n,source_sha256=sha(f),olean_sha256=sha(o),dependencies=deps,axioms=ax(log)));lookup[n]=o
 print(n,flush=True)
q=W/'Audit.lean'
names=['ExactPlaneCheckedProfile.'+t for t in ['solve_iff','returned','valid_path','chart_count']]+['ExactPlaneCheckedProfile.supported_path','ExactPlaneSectionCheckComplete.valid_iff_phys']
q.write_text('import ExactPlaneSemanticProfile\nimport ExactPlaneCheckedProfile\n'+''.join('#print axioms '+n+'\n' for n in names))
ax=run([lean,'-j1',q]);assert ax.count('[propext, Classical.choice, Quot.sound]')==len(names);(D/'axioms.log').write_text(ax)
controls=run([lean,'-j1',D/'controls.lean']);assert controls.splitlines()==['false','some 2','false','[2, 2, 10, 10, 42]'],controls;(D/'controls.log').write_text(controls)
(D/'receipt.json').write_text(json.dumps(dict(commit=C,source_count=90,new_modules=new,reused=reused,demo_controls=controls.splitlines(),baselines=baselines,producer_manifests={p:sha(prod/(p+'.sha256')) for p in ['profile-full','profile-increment']},axioms=ax.splitlines()),indent=2)+'\n')
