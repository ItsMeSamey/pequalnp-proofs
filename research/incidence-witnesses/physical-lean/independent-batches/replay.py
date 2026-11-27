from pathlib import Path as P
import os,re,json,sys,subprocess,time,hashlib
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();f=w/'fresh';prior=w/'prior'
known={}; prev={}
for name,h in [('review-q401','19885c592cd38f2b0178b3fe277c76b756b0884b25d33b3ca56beb718a59700a'),('review-q401-increment','1e4842385824637539c18566211590dd784e3e03331c01cf530f77c69e038108'),('review-q401-plus2','069212e67dd7fa75784e9eba5d88ab2b72b62e4365bd332c586df31d684edaa2')]:
 rd=d.parent/name;r=rd/'receipt.json';assert sha(r)==h;prev[name]=h;ow=P((rd/'workdir').read_text().strip())
 for n,v in json.loads(r.read_text())['modules'].items():
  o=n[:-5]+'.olean';p=ow/'fresh'/o;assert sha(p)==v['object'] and sha(ow/n)==v['source']; z=prior/o;z.parent.mkdir(exist_ok=True,parents=True)
  if not z.exists():z.symlink_to(p)
  known[n]=p
(f/'Research').mkdir(exist_ok=True)
for oldobj in (prior/'Research').glob('*.olean'):
 dest=f/'Research'/oldobj.name
 if not dest.exists():dest.symlink_to(oldobj)
 assert dest.resolve()==oldobj.resolve()
locks={'ten':('INCREMENT-10','3d9ffc82e2525cfc50f487efd311900fe0ad5d032f2ca486194a228c0914c5ce','d1e393589ce75e5fe93ed25716a3a0263395e3f0'),'marks':('INCREMENT-MARKS','f30f670ade769d075d3abd76d046c0c3196f9ef0fef0c3e5f388a380961637ab','e4ead8b0a3b9c84e2d8d0208cf3f6272c95a7469'),'round':('INCREMENT-ROUND','87060e929d93da451ebec3e966456e344b8bb17649fd22e25369560a852e7475','6e355d094d7a2213d4a11a3c398d4a84b8b5ee3a'),'hoist':('first-nine','1639f02ea2457853cf56faaf30305dc31caa5f2713ce415acd36bb3f12ff9a42','e4ead8b0a3b9c84e2d8d0208cf3f6272c95a7469')}
locks['fullhoist']=('all-lean','5b6e357837f67d5ae4254ea6f04a1c7164a1a0581e1bfe244208a9cc6fdf0cc2','8808fdae5012178edbd92c5485d4dac82eb7894b')
tasks={}; objects={}
for st,(nm,h,c) in locks.items():
 s=w/st;mf=s/(nm+'.sha256');assert sha(mf)==h
 for hh,n in [l.split() for l in mf.read_text().splitlines()]:
  if n.endswith('.olean'):
   key=P(n).name;assert key not in objects or objects[key]==hh;objects[key]=hh;continue
  if st=='fullhoist' and n in tasks:
   assert tasks[n][0]=='hoist' and sha(tasks[n][1]/n)==sha(s/n)==hh
   continue
  assert n not in known and n not in tasks and sha(s/n)==hh;tasks[n]=(st,s)
assert len(tasks)==33
def imports(p):return [n.replace('.','/')+'.lean' for n in re.findall(r'^import ((?:Hoist|Incidence|Protected|Research)[\w.]*)',p.read_text(),re.M)]
todo=[j for n,(_,s) in tasks.items() for j in imports(s/n) if j.startswith('Research/')]
while todo:
 n=todo.pop()
 if n in known or n in tasks:continue
 p=w/'native'/n;p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(subprocess.check_output(['git','-C','/workspace/pnp-research','show',locks['ten'][2]+':lean/'+n]));tasks[n]=('native',w/'native');todo+=imports(p)
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=':'.join(map(str,[f,prior,P('/dev/shm/gcycle-t2/mathlib'),*sorted(P('/workspace/pequalnp-proofs/lean/.lake/packages').glob('*/.lake/build/lib/lean'))]))
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
for n,r in rows.items():
 p=f/(n[:-5]+'.olean');assert sha(p)==r['object'];known[n]=p
for _ in range(int(sys.argv[1])):
 n=next((n for n,(_,s) in sorted(tasks.items(),key=lambda item: (item[1][0]!="native",list(tasks).index(item[0]))) if n not in known and set(imports(s/n))<=known.keys()),None)
 if n is None:break
 st,s=tasks[n];o=f/(n[:-5]+'.olean');o.parent.mkdir(exist_ok=True,parents=True); deps=run(['--deps',n],s).splitlines()
 for ip in imports(s/n):assert any(P(x).resolve()==known[ip].resolve() for x in deps)
 if st in ('hoist','fullhoist'):
  canon=P('/workspace/scratch/incidence-hoist');assert sha(canon/n)==sha(s/n);log=run(['--root='+str(canon),'-o',o,canon/n],canon)
 else:log=run(['-o',o,n],s)
 lg=d/(n[:-5].replace('/','-')+'.log');lg.write_text(log);assert 'sorryAx' not in log
 if st in ('hoist','fullhoist'):assert sha(canon/n)==sha(s/n) and sha(o)==objects[o.name] and log==(s/'receipts'/(n[:-5]+'.log')).read_text(),(n,sha(o),log)
 elif st=='native':assert sha(o)==sha(P('/workspace/scratch/incidence-release-check')/(n[:-5]+'.olean'))
 else:
  gold={P(p).suffix:h for h,p in [z.split() for z in (s/'producer'/(n[:-5]+'.sha256')).read_text().splitlines()]};assert gold=={'.lean':sha(s/n),'.olean':sha(o),'.log':sha(lg)},(n,gold,sha(o),log)
 rows[n]=dict(stage=st,source=sha(s/n),object=sha(o),log=sha(lg),deps=deps,axioms=re.findall(r"'([\w.]+)' depends on axioms",log));known[n]=o;lf.write_text(json.dumps(rows,indent=2)+'\n');print(n,flush=True)
for stage in locks:
 names=[n for n,(st,_) in tasks.items() if st==stage]; receipt=d/(stage+'-receipt.json')
 if any(n not in rows for n in names) or receipt.exists():continue
 axs=[]
 for n in names:
  text=(tasks[n][1]/n).read_text();ns=re.search(r'^namespace ([\w.]+)',text,re.M)[1]
  axs += [ns+'.'+x for x in re.findall(r'^theorem ([\w.\']+)',text,re.M)]
 p=d/(stage+'-axioms.lean');p.write_text(''.join('import '+n[:-5]+'\n' for n in names)+''.join('#print axioms '+a+'\n' for a in axs));z=run([p],w);(d/(stage+'-axioms.log')).write_text(z)
 assert 'sorryAx' not in z and set(re.findall(r"'([\w.']+)' (?:depends on axioms|does not depend on any axioms)",z))==set(axs)
 receipt.write_text(json.dumps(dict(lock=locks[stage],prior=prev,modules={n:rows[n] for n in names},public=axs,axioms=sha(d/(stage+'-axioms.log'))),indent=2)+'\n');print(stage+' PASS',sha(receipt))
if set(tasks)<=set(known):
 receipt=d/'receipt.json';receipt.write_text(json.dumps(dict(locks=locks,prior=prev,ledger=sha(lf),stages={k:sha(d/(k+'-receipt.json')) for k in locks},local=33,native=len(rows)-33),indent=2)+'\n');print('PASS',sha(receipt))
