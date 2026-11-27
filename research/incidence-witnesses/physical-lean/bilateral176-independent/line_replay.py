from line_inventory import *
import os,time
w=P((d/'workdir').read_text());f=w/'fresh';prior=w/'prior';srcroot=w/'line-src';srcroot.mkdir(exist_ok=True)
lf=d/'line-ledger.json';rows=json.loads(lf.read_text()) if lf.exists() else {}
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
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

knownO={}
for n,v in mods.items():
 k=n.replace('.','/');role=groups[n];path=P(known[k]) if role=='prior' else f/(k+'.olean')
 if path.exists():
  assert sha(path)==v['object'];knownO[n]=path
for _ in range(int(os.environ.get('REVIEW_BATCH','3'))):
 n=next((n for n,v in mods.items() if groups[n]=='new' and n not in rows and (not os.environ.get('REVIEW_TARGET') or n==os.environ['REVIEW_TARGET']) and all(j not in mods or j in knownO for j in v['imports'])),None)
 if n is None:break
 r=mods[n];name=n+'.lean';p=srcroot/name;p.write_bytes(z.read('src/'+name));pg=z.read(r['log_path']).decode() if r['log'] else ''
 # Canonical absolute compiler spelling matters for locations serialized in diagnostics/objects.
 dirs=[base/'incidence-line-warm',base/'incidence-witnesses',base/'incidence-q401',base/'incidence-warm-traces',base/'incidence-run-pin',base/'incidence-pin-hoist',base/'incidence-hoist']
 can=next((q/name for q in dirs if (q/name).exists() and sha(q/name)==r['src']),None)
 absolute=can is not None and (str(can) in pg or ('/objects/' in r['object_path'] and can.parent.name!='incidence-q401'))
 if absolute:p=can
 deps=run(['--deps',p],p.parent).splitlines()
 for j in r['imports']:
  if j in mods:assert any(P(x).resolve()==knownO[j].resolve() for x in deps)
 o=f/(n+'.olean');log=run(['--root='+str(p.parent),'-o',o,p if absolute else p.name],p.parent);(d/(n+'.log')).write_text(log)
 assert sha(o)==r['object'] and sha(p)==r['src'],(n,sha(o),r['object'])
 if r['log']:assert log==pg,n
 assert 'sorryAx' not in log;rows[n]=dict(source=sha(p),object=sha(o),log=sha(d/(n+'.log')),deps={q:sha(P(q)) for q in deps})
 knownO[n]=o;lf.write_text(json.dumps(rows,indent=2)+'\n');print(len(rows),n,flush=True)
