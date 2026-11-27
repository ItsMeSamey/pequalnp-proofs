"""One serialized checkpoint. frozen.json records commit, repository path and object hash per module."""
from inventory import *
import subprocess,sys,time,os,tempfile
d=P(__file__).resolve().parent;wf=d/'workdir'
if not wf.exists():wf.write_text(tempfile.mkdtemp(prefix='review-actual-',dir='/dev/shm'))
w=P(wf.read_text());f=w/'fresh';f.mkdir(exist_ok=True); prior=w/'prior';prior.mkdir(exist_ok=True)
locked=json.loads((d/'frozen.json').read_text()); lf=d/'ledger.json';rows=json.loads(lf.read_text()) if lf.exists() else {}
for n,src in known.items():
 o=prior/(n+'.olean');o.parent.mkdir(exist_ok=True,parents=True)
 if not o.exists():o.symlink_to(src)
 assert o.resolve()==P(src).resolve()
for n,r in rows.items():assert sha(f/(n+'.olean'))==r['object']==locked[n]['object']
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
env=os.environ|{'LEAN_PATH':':'.join(map(str,[f,prior,P('/dev/shm/gcycle-t2/mathlib'),*sorted(P('/workspace/pequalnp-proofs/lean/.lake/packages').glob('*/.lake/build/lib/lean'))]))}
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

for count in range(int(os.environ.get('REVIEW_BATCH','3'))):
 n=next((n for n,t in new.items() if n in locked and n not in rows and (not os.environ.get('REVIEW_TARGET') or n==os.environ['REVIEW_TARGET']) and all(y in rows or y in known for y in t['imports'])),None)
 if n is None:break
 b=locked[n];s=P(new[n]['source']); raw=subprocess.check_output(['git','-C','/workspace/pnp-research','show',b['commit']+':'+b['path']])
 if 'archive' in b:
  import io,zipfile
  assert hashlib.sha256(raw).hexdigest()==b['archive']
  raw=zipfile.ZipFile(io.BytesIO(raw)).read('sources/'+n+'.lean')
 assert raw==s.read_bytes() and sha(s)==b['source']
 deps=run(['--deps',s],s.parent).splitlines()
 for y in new[n]['imports']:
  want=f/(y+'.olean') if y in rows else P(known[y]);assert any(P(p).resolve()==want.resolve() for p in deps)
 o=f/(n+'.olean');patharg=s if b.get('absolute',True) else s.name
 log=run(['--root='+str(s.parent),'-o',o,patharg],s.parent)
 (d/(n+'.log')).write_text(log);assert sha(s)==b['source'] and 'sorryAx' not in log
 assert sha(o)==b['object'],(n,sha(o),b['object'])
 if 'log' in b:assert sha(d/(n+'.log'))==b['log']
 rows[n]=dict(commit=b['commit'],source=sha(s),object=sha(o),log=sha(d/(n+'.log')),deps={p:sha(P(p)) for p in deps})
 lf.write_text(json.dumps(rows,indent=2)+'\n');print(len(rows),n,flush=True)
