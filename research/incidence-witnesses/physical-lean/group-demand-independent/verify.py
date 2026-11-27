from pathlib import Path as P
import os,json,hashlib,subprocess,tempfile,io,zipfile,re
from resource_guard import compile_guarded
d=P(__file__).resolve().parent; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ref='a72dd601c52589b8f739c5920b68791159e94971:research/incidence-witnesses/physical-lean/group-demand-eight.zip'
b=subprocess.check_output(['git','-C','/workspace/pnp-research','show',ref]);assert hashlib.sha256(b).hexdigest()=='4ac3dcf15ef48945aa95625bf4026555cf17b1d0190c9608516f4c31d09ff71d'
z=zipfile.ZipFile(io.BytesIO(b));deps=json.loads(z.read('q401-dependencies.json'));prev=json.loads((d.parent/'review-q401-actual/scalar/all255.json').read_text());wf=d/'workdir'
if not wf.exists():wf.write_text(tempfile.mkdtemp(prefix='review-5r6v-',dir='/dev/shm'))
w=P(wf.read_text()); f=w/'fresh';f.mkdir(exist_ok=True);p=w/'prior';p.mkdir(exist_ok=True);s=w/'src';s.mkdir(exist_ok=True)
for n,x in deps.items():
 t=P(x['path']);assert sha(t)==prev[n]['object']==x['sha'];y=p/(n.replace('.','/')+'.olean');y.parent.mkdir(parents=True,exist_ok=True)
 if not y.exists():y.symlink_to(t)
 assert y.resolve()==t.resolve()
(d/'prior.json').write_text(json.dumps(deps,indent=2)+'\n');assert len(deps)==18
env=os.environ|dict(LEAN_PATH=':'.join(map(str,[f,p,P('/dev/shm/gcycle-t2/mathlib'),*sorted(P('/workspace/pequalnp-proofs/lean/.lake/packages').glob('*/.lake/build/lib/lean'))])))
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
alln=[q[:-5] for q in z.namelist() if q.endswith('.lean')];lf=d/'ledger.json';rr=json.loads(lf.read_text()) if lf.exists() else {}
for n,row in rr.items():assert sha(f/(n+'.olean'))==row['object']
for _ in range(3):
 for n in alln:
  if n in rr:continue
  src=z.read(n+'.lean');imports=re.findall(r'^import ([\w.]+)',src.decode(),re.M)
  if all(j not in alln or j in rr for j in imports):break
 else:break
 file=s/(n+'.lean');file.write_bytes(src);out=f/(n+'.olean');lock={P(j).suffix:h for h,j in (a.split() for a in z.read('receipts/'+n+'.sha256').decode().splitlines())};assert sha(file)==lock['.lean']
 use=compile_guarded(lean,['--deps',file.name],s,env).splitlines()
 for j in imports:
  if j in alln or j in deps:
   t=(f if j in alln else p)/(j.replace('.','/')+'.olean');assert any(P(q).resolve()==t.resolve() for q in use)
 log=compile_guarded(lean,['-o',out,file.name],s,env);(d/(n+'.log')).write_text(log);assert sha(out)==lock['.olean'] and log.encode()==z.read('receipts/'+n+'.log') and 'sorryAx' not in log
 rr[n]=dict(source=sha(file),object=sha(out),log=sha(d/(n+'.log')),deps={q:sha(P(q)) for q in use});lf.write_text(json.dumps(rr,indent=2)+'\n');print(len(rr),n,flush=True)
if len(rr)==8:
 r=d/'receipt.json';r.write_text(json.dumps(dict(ref=ref,archive=hashlib.sha256(b).hexdigest(),prior=sha(d/'prior.json'),fresh=8,prior_count=18,ledger=sha(lf),guard=sha(d/'resource_guard.py')),indent=2)+'\n');print(sha(r))
