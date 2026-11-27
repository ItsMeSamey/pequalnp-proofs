from pathlib import Path as P
import os,re,json,subprocess,hashlib,time
d=P(__file__).resolve().parent; w=P((d/'workdir').read_text().strip());f=w/'fresh'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
commit='23c996386fe9c83d2cc285c1051e63e020bcc56f'
assert sha(w/'SOURCES.sha256')=='0d9a23d84e772971de6eb1f1ad3ba3d66dda5cbce5a9e1d5819008b81f9847e6'
local={p:h for h,p in [line.split() for line in (w/'SOURCES.sha256').read_text().splitlines()]};assert len(local)==12
native=['Research/IncidenceBound.lean','Research/SparseIncidence.lean','Research/CircuitRewire.lean']
for n in native:assert subprocess.check_output(['git','-C','/workspace/pnp-research','show',commit+':lean/'+n])==(w/n).read_bytes()
for n,h in local.items():assert sha(w/n)==h
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
pkg=P('/workspace/pequalnp-proofs/lean/.lake/packages'); mlib=P('/dev/shm/gcycle-t2/mathlib')
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env['LEAN_PATH']=':'.join(map(str,[f,mlib,*sorted(pkg.glob('*/.lake/build/lib/lean'))]))
def run(args):
 q=subprocess.Popen([lean,'-j1',*args],env=env,cwd=w,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 start=time.monotonic();peak=0; cg=P("/sys/fs/cgroup"); events=lambda:sum(int(l.split()[1]) for l in (cg/"memory.events").read_text().splitlines() if l.split()[0] in ("oom","oom_kill"));old=events()
 while q.poll() is None:
  try:
   roll={l.split()[0]:int(l.split()[1]) for l in P('/proc',str(q.pid),'smaps_rollup').read_text().splitlines() if len(l.split())>1 and l.split()[1].isdigit()}
   peak=max(peak,roll.get('Pss_Anon:',0))
   mem={k:int(v) for k,v in (l.split() for l in (cg/"memory.stat").read_text().splitlines())}
   if peak>563200 or time.monotonic()-start>45 or events()>old or (int((cg/"memory.current").read_text())>8455716864 and mem["file"]-mem["shmem"]<805306368):q.kill()
  except (FileNotFoundError,ProcessLookupError):pass
  time.sleep(.15)
 z=q.communicate()[0];assert q.returncode==0,(args,q.returncode,peak,z)
 return z
done={};pub=[];depslib={}; left=[*native,*local]
while left:
 n=next(n for n in left if all(x.replace('.','/')+'.lean' in done for x in re.findall(r'^import ((?:Research|Incidence|Protected)[\w.]*)',(w/n).read_text(),re.M)))
 obj=f/(n[:-5]+'.olean');assert not obj.exists()
 deps=run(['--deps',n]).splitlines()
 for dep in map(P,deps):
  assert dep.exists()
  if dep.name.startswith(('Incidence','Protected','CircuitRewire','SparseIncidence')) and ('/Mathlib/' not in str(dep)):
   assert dep.is_relative_to(f) and str(dep.relative_to(f).with_suffix('.lean')) in done
  else: depslib[str(dep)]=sha(dep)
 z=run(['-o',obj,n]); lg=d/(n.replace('/','-')[:-5]+'.log');lg.write_text(z)
 prior=None
 if n in local:
  gold=w/'producer'/(n[:-5]+'.sha256'); wanted={P(v).suffix:h for h,v in [l.split() for l in gold.read_text().splitlines()]}
  assert wanted=={'.lean':sha(w/n),'.olean':sha(obj),'.log':sha(lg)},(n,sha(obj),sha(lg),wanted)
  assert z==(w/'producer'/(n[:-5]+'.log')).read_text()
  ns=re.search(r'^namespace ([\w.]+)',(w/n).read_text(),re.M)[1]
  pub.extend([ns+'.'+nm for nm in re.findall(r'^theorem ([\w\']+)',(w/n).read_text(),re.M)])
 else: prior=sha(P('/workspace/scratch/incidence-release-check')/(n[:-5]+'.olean'))
 done[n]=dict(source=sha(w/n),object=sha(obj),log=sha(lg),deps=deps,prior_native_obj=prior)
 left.remove(n);print(n,flush=True)
 if len(done)%3==0 and len(done)<15:
  (d/('checkpoint-'+str(len(done)))).touch()
  while not (d/('go-'+str(len(done)))).exists():time.sleep(.25)
assert len(pub)==44
probe=d/'axioms.lean'; probe.write_text(''.join('import '+n[:-5]+'\n' for n in local)+''.join('#print axioms '+nm+'\n' for nm in pub))
z=run([probe]);(d/'axioms.log').write_text(z);assert len(z.splitlines())==len(pub) and 'sorryAx' not in z
(d/'receipt.json').write_text(json.dumps(dict(commit=commit,manifest=sha(w/'SOURCES.sha256'),lean=sha(lean),modules=done,depslib=depslib,public=pub,axioms=sha(d/'axioms.log')),indent=2)+'\n')
print('PASS',len(local),len(native),len(pub),sha(d/'receipt.json'),flush=True)
