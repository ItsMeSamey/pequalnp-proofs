from pathlib import Path as P
import sys,os,json,hashlib,subprocess,re,time
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip())
stage='validator';commit='8c292dc3d7033a38aaa148997140741639b00d9b';mdig='039bb9a1fd5479e843d736b95126994aaf9be1e517383ded737efffbdbfea57c';ldig=mdig;s=w/'lean';prod='receipts';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(w/'final.sha256')==mdig
def mf(f):return {n:h for h,n in (l.split() for l in (w/f).read_text().splitlines())}
for lock in ['final.sha256','release.sha256','all-lean.sha256','core.sha256']:
 for n,h in mf(lock).items():
  if '/objects/' not in n:assert sha(w/n)==h
prodhash={P(n).name:h for lock in ['all-lean.sha256','final.sha256','release.sha256'] for n,h in mf(lock).items()}
srcs={n:h for n,h in prodhash.items() if n.endswith('.lean')};assert len(srcs)==7
fresh=w/'fresh';prior=w/'prior'
nine=d.parent/'review-three-name-rejection';q=nine/'receipt.json'; assert sha(q)=='5c84515b600b7273f265f0e5714b2e6b2b042809a0c4440841adeba1b2b47402'
r=json.loads(q.read_text()); prev=P((nine/'workdir').read_text().strip());known={}
def link(n,path,h):
 assert sha(path)==h
 dest=prior/(n+'.olean')
 if not dest.exists():dest.symlink_to(path)
 assert dest.resolve()==path.resolve()
 known[n]=path
for n,row in r['modules'].items():
 assert sha(prev/'lean'/(n+'.lean'))==row['source']
 link(n,prev/'fresh-canonical'/(n+'.olean'),row['object'])
g=d.parent/'review-plane-gaussian'; gr=g/'receipt.json'
assert sha(gr)=='e5044cd45b4e0a39472c77bff59f451eacb7f3b3f58e3e25a0c2003ca61b3f93'
n='ExactPlaneGaussian'; z=next(x for x in json.loads(gr.read_text())['new_modules'] if x['module']==n)
gw=P((g/'workdir').read_text().strip()); link(n,gw/'fresh'/(n+'.olean'),z['olean_sha256'])
rd=d.parent/'review-three-name-refinement';rw=P((rd/'workdir').read_text().strip())
for st,expected in [('core','1885b2958d49a3ced977d5ebe503081784c43bf5c080f1fb6fe168b761b462af'),('fixture','71ba06e1f71547b39dd5b81d2f31458d5133592903fc239151481fc5a48b4a46')]:
 rec=rd/(st+'-receipt.json');assert sha(rec)==expected
 prev=json.loads(rec.read_text())
 for n,v in prev['modules'].items():
  assert sha(rw/st/(n+'.lean'))==v['source'];link(n,rw/'fresh'/(n+'.olean'),v['object'])
gd=d.parent/'review-three-name-generic';gw=P((gd/'workdir').read_text().strip())
for st,expect in [('generic','a262a43a9aa8e702ccb60c2ce634e6cca72af2e92be5df68f3c4f001e3d289b4'),('samples','89bd71773962000d71950884188e3d0584236268142175977988ce7d9b034e6e')]:
 rec=gd/(st+'-receipt.json');assert sha(rec)==expect
 for n,v in json.loads(rec.read_text())['modules'].items():
  assert sha(gw/'final/lean'/(n+'.lean'))==v['source'];link(n,gw/'fresh'/(n+'.olean'),v['object'])
base=P('/workspace/scratch/three-name-validator/lean');pkg=P('/workspace/pequalnp-proofs/lean/.lake/packages');lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
assert sha(lean)==r['lean']
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=':'.join(map(str,[fresh,prior,*sorted(pkg.glob('*/.lake/build/lib/lean'))]))
def run(args,timeout=75):
 start=time.monotonic()
 cg=P('/sys/fs/cgroup'); oom=lambda:sum(int(l.split()[1]) for l in (cg/'memory.events').read_text().splitlines() if l.split()[0] in ('oom','oom_kill'))
 old=oom(); guard=None;peak=0
 p=subprocess.Popen([lean,'-j1','--root='+str(base),*args],cwd=base,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 while p.poll() is None:
  proc=P('/proc')/str(p.pid)
  try:
   roll={l.split()[0]:int(l.split()[1]) for l in (proc/'smaps_rollup').read_text().splitlines() if len(l.split())>1 and l.split()[1].isdigit()}
   mem={k:int(v) for k,v in (l.split() for l in (cg/'memory.stat').read_text().splitlines())}
   anon=roll.get('Pss_Anon:',0); peak=max(peak,anon)
   if anon>563200 or oom()>old or (int((cg/'memory.current').read_text())>8455716864 and mem['file']-mem['shmem']<805306368) or time.monotonic()-start>timeout: guard=(anon,oom(),round(time.monotonic()-start,2));p.kill()
  except (ProcessLookupError,FileNotFoundError):pass
  time.sleep(.2)
 out=p.communicate()[0]
 with (d/(stage+'-guards.jsonl')).open('a') as log:print(json.dumps(dict(last=str(args[-1]),exit=p.returncode,anon_peak_KiB=peak,guard=guard)),file=log)
 assert p.returncode==0,(args,guard,out)
 return out
rows={};ax=[]
pending={P(n).stem for n in srcs if P(n).stem not in known}
while pending:
 n=next(n for n in sorted(pending) if set(re.findall(r'^import ((?:ThreeName|ExactPlane)\w+)',(s/(n+'.lean')).read_text(),re.M))<=known.keys())
 fn=n+'.lean';f=base/fn;obj=fresh/(n+'.olean');h=srcs[fn];assert sha(f)==sha(s/fn)==prodhash[fn]==h
 deps=run(['--deps',s/fn]).splitlines()
 for pp in map(P,deps):
  assert pp.exists()
  if pp.name.startswith(('ThreeName','ExactPlane')):assert pp.resolve()==known[pp.stem].resolve()
 logpath=d/(n+'.log')
 if obj.exists():
  assert sha(obj)==prodhash[obj.name] and logpath.exists()
  out=logpath.read_text()
 else:
  out=run(['-o',obj,f]);logpath.write_text(out)
 if n=='ThreeNameDenseControls':
  runtime=run(['--run',f]);(d/'runtime.log').write_text(runtime);assert runtime==(s/prod/(n+'.log')).read_text() and len(runtime.splitlines())==15
 else:assert out==(s/prod/(n+'.log')).read_text()
 assert sha(f)==h and sha(obj)==prodhash[obj.name],(n,sha(obj),out)
 rows[n]=dict(source=h,object=sha(obj),log=sha(d/(n+'.log')),deps=deps); ax+=re.findall(r"'([\w.]+)' depends on axioms",out);known[n]=obj;pending.remove(n);print(n,flush=True)
 if len(rows) in (3,6):
  (d/('checkpoint-'+str(len(rows)))).touch()
  while not (d/('go-'+str(len(rows)))).exists():time.sleep(.25)
probe=d/(stage+'-axioms.lean');probe.write_text(''.join('import '+n+'\n' for n in rows)+''.join('#print axioms '+nm+'\n' for nm in ax))
out=run([probe]);(d/(stage+'-axioms.log')).write_text(out)
reports=re.findall(r"'([\w.]+)' depends on axioms: *\[([^\]]+)\]",out,re.S)
assert [n for n,_ in reports]==ax and all(set(h.strip() for h in items.split(','))<={'propext','Classical.choice','Quot.sound'} for _,items in reports)
receipt=d/(stage+'-receipt.json')
receipt.write_text(json.dumps(dict(commit=commit,manifest=mdig,objects_lock=ldig,old_nine=sha(q),gaussian=sha(gr),modules=rows,axioms=ax,axioms_sha256=sha(d/(stage+'-axioms.log'))),indent=2)+'\n')
print('PASS',len(rows),len(ax),sha(receipt),flush=True)
