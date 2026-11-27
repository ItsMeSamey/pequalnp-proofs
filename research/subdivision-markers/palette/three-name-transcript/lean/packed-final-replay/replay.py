from pathlib import Path as P
import sys,os,json,hashlib,subprocess,re,time
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip())
stage,commit,manifest,mdig,prod,ldig=sys.argv[1:]
s=w/stage; lp=s/prod/'digests.txt'; assert s.is_dir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(s/manifest)==mdig and sha(lp)==ldig
def dig(path):return {P(n).name:h for h,n in [s.split() for s in path.read_text().splitlines()]}
srcs=dig(s/manifest); prodhash=dig(lp);fresh=w/'fresh';prior=w/'prior'
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
if stage!='core':
 core=json.loads((d/'core-receipt.json').read_text())
 for n,row in core['modules'].items():
  obj=fresh/(n+'.olean');assert sha(obj)==row['object']; known[n]=obj
base=P('/workspace/scratch/three-name-refinement/lean');pkg=P('/workspace/pequalnp-proofs/lean/.lake/packages');lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
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
 fn=n+'.lean';f=base/fn;obj=fresh/(n+'.olean');h=srcs[fn];assert sha(f)==sha(s/fn)==prodhash[fn]==h and not obj.exists()
 deps=run(['--deps',s/fn]).splitlines()
 for pp in map(P,deps):
  assert pp.exists()
  if pp.name.startswith(('ThreeName','ExactPlane')):assert pp.resolve()==known[pp.stem].resolve()
 out=run(['-o',obj,f]);(d/(n+'.log')).write_text(out)
 assert sha(f)==h and sha(obj)==prodhash[obj.name] and out==(s/prod/(n+'.log')).read_text(),(n,sha(obj),out)
 rows[n]=dict(source=h,object=sha(obj),log=sha(d/(n+'.log')),deps=deps); ax+=re.findall(r"'([\w.]+)' depends on axioms",out);known[n]=obj;pending.remove(n);print(n,flush=True)
probe=d/(stage+'-axioms.lean');probe.write_text(''.join('import '+n+'\n' for n in rows)+''.join('#print axioms '+nm+'\n' for nm in ax))
out=run([probe]);(d/(stage+'-axioms.log')).write_text(out)
assert len(out.splitlines())==len(ax) and 'sorryAx' not in out
receipt=d/(stage+'-receipt.json')
receipt.write_text(json.dumps(dict(commit=commit,manifest=mdig,objects_lock=ldig,old_nine=sha(q),gaussian=sha(gr),modules=rows,axioms=ax,axioms_sha256=sha(d/(stage+'-axioms.log'))),indent=2)+'\n')
print('PASS',len(rows),len(ax),sha(receipt),flush=True)
