from pathlib import Path as P
import json,hashlib,subprocess,sys,os,tempfile,re,time
d=P(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
wf=d/'workdir'
if not wf.exists():wf.write_text(tempfile.mkdtemp(prefix='review-pinrun-',dir='/dev/shm'))
w=P(wf.read_text());f=w/'fresh';f.mkdir(exist_ok=True)
git=lambda ref:subprocess.check_output(['git','-C','/workspace/pnp-research','show',ref])
locks=[('pin-hoist','f07b3ab79fa8de3da5de7f3ba1e64fb72cdaa09d','all-lean','00a8f009497e0787dcd8b370ad8e185fe8b54f8a76108e318c4da8d83d3ade8f'),('run-pin','a422c1cd07e0b85996ae5fe6791b82aafc1a4eb3','run-pin','9fc76941dcc6be789143a5d32f84919e3851dd1c6213162b471435a321e21232'),('weighted-plane','306e19b80026cdf69b98a3df8737da17feb11846','weighted-plane','9cb9c480a276e6c56198cdc4eef749402f2c34f6bcb8365d2832c48d72910f10')]
tasks={};known={};expected={}
for st,c,nm,h in locks:
 s=P('/workspace/scratch/incidence-'+st);prefix=c+':research/incidence-witnesses/physical-lean/'+st+'/'
 manifest=git(prefix+nm+'.sha256');assert hashlib.sha256(manifest).hexdigest()==h
 entries={p:a for a,p in (l.split() for l in manifest.decode().splitlines())}
 if st!='pin-hoist':
  m=nm+'-manifest.json';data=git(prefix+m);assert hashlib.sha256(data).hexdigest()==entries[m]
  for row in json.loads(data)['modules']:entries.update(row.get('sha256',{}))
  entries.update(json.loads(data).get('files',{}))
 for p,hh in entries.copy().items():
  if not p.endswith('.lean'):continue
  n=P(p).stem;assert sha(s/p)==hh and (s/p).read_bytes()==git(prefix+p);tasks[n]=(st,s,hh);expected[n]=entries['objects/'+n+'.olean']
prior=P('/workspace/scratch/review-q401-batches');old=P((prior/'workdir').read_text().strip())
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
paths=[f,old/'fresh',old/'prior',P('/workspace/scratch/incidence-release-check'),P('/dev/shm/incidence-ledger-olean'),P('/dev/shm/incidence-q401-physical'),P('/workspace/scratch'),P('/dev/shm/gcycle-t2/mathlib'),*sorted(P('/workspace/pequalnp-proofs/lean/.lake/packages').glob('*/.lake/build/lib/lean'))]
env=os.environ|{'LEAN_PATH':':'.join(map(str,paths))}
def run(args,cwd):
 q=subprocess.Popen([lean,'-j1',*args],env=env,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
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

lf=d/'ledger.json';rows=json.loads(lf.read_text()) if lf.exists() else {}
for n,row in rows.items():assert sha(f/(n+'.olean'))==row['object']==expected[n]
for _ in range(3):
 for n,(st,s,hh) in tasks.items():
  src=s/(n+'.lean');im=re.findall(r'^import ([\w.]+)',src.read_text(),re.M)
  if n not in rows and all(j not in tasks or j in rows for j in im):break
 else:break
 deps=run(['--deps',src],s).splitlines()
 for j in im:
  if j in tasks:assert str(f/(j+'.olean')) in deps
 o=f/(n+'.olean');log=run(['--root='+str(s),'-o',o,src],s);assert sha(src)==hh and sha(o)==expected[n],(n,sha(o),expected[n])
 assert log==(s/'receipts'/(n+'.log')).read_text() and 'sorryAx' not in log
 (d/(n+'.log')).write_text(log)
 rows[n]=dict(stage=st,source=hh,object=sha(o),deps={p:sha(P(p)) for p in deps},log=sha(d/(n+'.log')))
 lf.write_text(json.dumps(rows,indent=2)+'\n');print(len(rows),n,flush=True)
