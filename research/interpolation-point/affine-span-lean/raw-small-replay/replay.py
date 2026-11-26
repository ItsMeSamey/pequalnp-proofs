from pathlib import Path
import subprocess,hashlib,json,tempfile,re,os
D=Path(__file__).resolve().parent;oldD=D.parent/'review-plane-raw';oldR=Path((oldD/'workdir').read_text().strip());oldO=oldR/'fresh';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(oldD/'receipt.json')=='91b70c85dc73613e9f3feaf04fa82ca46ca2cebb977020b5fde14b7df9a93794';old=json.loads((oldD/'receipt.json').read_text())
c='2ef6e3220e7738948c646829c1bd3ab268670eb1';rel=old['rel'];roo=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-raw-small-'));s=roo/rel;o=roo/'fresh';o.mkdir();(D/'workdir').write_text(str(roo)+'\n')
repo='/workspace/pnp-research';p=subprocess.Popen(['git','-C',repo,'archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',roo],stdin=p.stdout,check=True);assert p.wait()==0
assert sha(s/'RAW-SMALL-INCREMENT.sha256')=='39a3f2c66652710319b849d4a2030900f1184c0f73372bc8bbf7b4a4d5489a27'
assert sha(s/'RAW-SOURCES.sha256')==old['manifest_sha256']
prior={}
for m in old['modules']:
 name=m['module'];obj=oldO/(name+'.olean');assert sha(obj)==m['olean_sha256'] and sha(s/(name+'.lean'))==m['source_sha256'];prior[name]=obj
for f in ['prerequisites.json','reused-prerequisites.json']:
 for m in json.loads((oldD/f).read_text()):assert sha(Path(m['path']))==m['olean_sha256']
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');pp=Path('/workspace/pequalnp-proofs/lean');libs=[o,oldO,oldR/'prerequisites']+sorted((pp/'.lake/packages').glob('*/.lake/build/lib/lean'));env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,libs))
assert sha(lean)==old['lean_sha256'];rec=[];cmd=[lean,'-j1','--root',s]
for line in (s/'RAW-SMALL-INCREMENT.sha256').read_text().splitlines():
 h,f=line.split();f=s/f;name=f.stem;assert sha(f)==h;target=o/(name+'.olean')
 deps=subprocess.check_output(cmd+['--deps',f],text=True,cwd=s,env=env).splitlines()
 for dep in deps:
  d=Path(dep);assert d.is_file()
  if d.name.startswith('ExactPlane'):assert d==prior[d.stem]
 with (D/(name+'.log')).open('w') as w:subprocess.run(cmd+['-o',target,f.name],cwd=s,env=env,stdout=w,stderr=subprocess.STDOUT,check=True)
 ax=lambda p:[l for l in p.read_text().splitlines() if 'depends on axioms:' in l];reports=ax(D/(name+'.log'));assert reports==ax(s/'producer'/(name+'.log')) and reports
 rec.append(dict(module=name,source_sha256=h,olean_sha256=sha(target),deps=deps,axioms=reports));prior[name]=target;print(name,flush=True)
q=roo/'Probe.lean';q.write_text('import ExactPlaneRawSmallDecision\n#print axioms ExactPlaneSmallWitness.thin\n#print axioms ExactPlaneAcceptedSmallWitness.raw_small_decision\n')
r=subprocess.check_output([lean,'-j1',q],cwd=s,env=env,text=True);assert r.count('[propext, Classical.choice, Quot.sound]')==2;(D/'canonical-axioms.log').write_text(r)
(D/'receipt.json').write_text(json.dumps(dict(commit=c,rel=rel,increment_sha256=sha(s/'RAW-SMALL-INCREMENT.sha256'),baseline_receipt_sha256=sha(oldD/'receipt.json'),rehashed_baseline_objects=len(old['modules']),modules=rec),indent=2)+'\n')
(D/'statement.txt').write_text('theorem raw_small_decision'+(s/'ExactPlaneRawSmallDecision.lean').read_text().split('theorem raw_small_decision',1)[1].split(' := by',1)[0]+'\n')
