from pathlib import Path
import subprocess,hashlib,json,tempfile,re,os
D=Path(__file__).resolve().parent;oldD=D.parent/'review-plane-raw';oldR=Path((oldD/'workdir').read_text().strip());oldO=oldR/'fresh';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(oldD/'receipt.json')=='91b70c85dc73613e9f3feaf04fa82ca46ca2cebb977020b5fde14b7df9a93794';old=json.loads((oldD/'receipt.json').read_text())
c='fef6c8c272365df95d56bd81ad5c117d2f5f49cc';rel=old['rel'];roo=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-executable-'));s=roo/rel;o=roo/'fresh';o.mkdir();(D/'workdir').write_text(str(roo)+'\n')
repo='/workspace/pnp-research';p=subprocess.Popen(['git','-C',repo,'archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',roo],stdin=p.stdout,check=True);assert p.wait()==0
assert sha(s/'EXECUTABLE-INCREMENT.sha256')=='f1762d6873ad241d5e22f3af6de1477bd143ec2c556e5c4a97c94e59a6958612'
assert sha(s/'RAW-SOURCES.sha256')==old['manifest_sha256']
prior={}
for m in old['modules']:
 name=m['module'];obj=oldO/(name+'.olean');assert sha(obj)==m['olean_sha256'] and sha(s/(name+'.lean'))==m['source_sha256'];prior[name]=obj
smallD=D.parent/'review-plane-raw-small';smallO=Path((smallD/'workdir').read_text().strip())/'fresh';assert sha(smallD/'receipt.json')=='26fc4fe5e3eb164a499abfb41ded15366195c79defa464ea63bc5abfc06581ea';small=json.loads((smallD/'receipt.json').read_text())
for m in small['modules']:
 name=m['module'];obj=smallO/(name+'.olean');assert sha(obj)==m['olean_sha256'] and sha(s/(name+'.lean'))==m['source_sha256'];prior[name]=obj
for f in ['prerequisites.json','reused-prerequisites.json']:
 for m in json.loads((oldD/f).read_text()):assert sha(Path(m['path']))==m['olean_sha256']
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');pp=Path('/workspace/pequalnp-proofs/lean');libs=[o,smallO,oldO,oldR/'prerequisites']+sorted((pp/'.lake/packages').glob('*/.lake/build/lib/lean'));env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,libs))
assert sha(lean)==old['lean_sha256'];rec=[];cmd=[lean,'-j1','--root',s]
for line in (s/'EXECUTABLE-INCREMENT.sha256').read_text().splitlines():
 h,f=line.split();f=s/f;name=f.stem;assert sha(f)==h;target=o/(name+'.olean')
 deps=subprocess.check_output(cmd+['--deps',f],text=True,cwd=s,env=env).splitlines()
 for dep in deps:
  d=Path(dep);assert d.is_file()
  if d.name.startswith('ExactPlane'):assert d==prior[d.stem]
 with (D/(name+'.log')).open('w') as w:subprocess.run(cmd+['-o',target,f.name],cwd=s,env=env,stdout=w,stderr=subprocess.STDOUT,check=True)
 ax=lambda p:[l for l in p.read_text().splitlines() if 'depends on axioms:' in l];reports=ax(D/(name+'.log'));assert reports==ax(s/'producer'/(name+'.log')) and reports
 rec.append(dict(module=name,source_sha256=h,olean_sha256=sha(target),deps=deps,axioms=reports));prior[name]=target;print(name,flush=True)
demo=s/'ExactPlaneSelectorExamples.lean';dlog=subprocess.check_output(cmd+[demo.name],cwd=s,env=env,text=True);assert dlog==(s/'producer/ExactPlaneSelectorExamples.log').read_text()=='some 3\nsome 2\nfalse\n';(D/'demo.log').write_text(dlog)
q=roo/'Probe.lean';q.write_text('import ExactPlaneExecutableCompression\n#print axioms ExactPlaneExecutableSelector.exists_complete_seed\n#print axioms ExactPlaneExecutableSelector.runCompact_spec\n');report=subprocess.check_output([lean,'-j1',q],env=env,cwd=s,text=True);assert report.count('[propext, Classical.choice, Quot.sound]')==2;(D/'canonical-axioms.log').write_text(report)
(D/'receipt.json').write_text(json.dumps(dict(commit=c,rel=rel,increment_sha256=sha(s/'EXECUTABLE-INCREMENT.sha256'),baseline_receipt_sha256=sha(oldD/'receipt.json'),small_receipt_sha256=sha(smallD/'receipt.json'),rehashed_baseline_objects=len(old['modules'])+len(small['modules']),modules=rec,demo_source_sha256=sha(demo),demo=dlog.strip().splitlines()),indent=2)+'\n')
