from pathlib import Path
import hashlib,subprocess,tempfile,os,json,re
D=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();c='1147c14916ac449aadaa71f35e8f5f78b80b887e';rel='research/interpolation-point/affine-span-lean';R=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-gaussian-'));(D/'workdir').write_text(str(R)+'\n');S=R/rel;O=R/'fresh';O.mkdir()
p=subprocess.Popen(['git','-C','/workspace/pnp-research','archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',R],stdin=p.stdout,check=True);assert p.wait()==0
assert sha(S/'EAGER-SOURCES.sha256')=='0d5f15578580c51cd40741ad348442bbc3054c806bd8bfa6b967c33271b2ad92'
rows={Path(l.split()[1]).stem:l.split()[0] for l in (S/'EAGER-SOURCES.sha256').read_text().splitlines()};assert len(rows)==52
for name,h in rows.items():assert sha(S/(name+'.lean'))==h
roots=[];lookup={};receipts={}
for folder,hh in [('review-plane-executable','c3ea13a5cb43e45e505d3b00fbf95eb881b4a858bb55e0d4539ad27e002d7bcf'),('review-plane-raw-small','26fc4fe5e3eb164a499abfb41ded15366195c79defa464ea63bc5abfc06581ea'),('review-plane-raw','91b70c85dc73613e9f3feaf04fa82ca46ca2cebb977020b5fde14b7df9a93794')]:
 d=D.parent/folder;assert sha(d/'receipt.json')==hh;receipts[folder]=hh;rr=json.loads((d/'receipt.json').read_text());path=Path((d/'workdir').read_text().strip());roots.append(path/'fresh')
 for m in rr['modules']:
  n=m['module']
  if n in rows:
   obj=path/'fresh'/(n+'.olean');assert sha(obj)==m['olean_sha256'] and rows[n]==m['source_sha256'];lookup[n]=obj
assert len(lookup)==39,len(lookup)
for filename in ['prerequisites.json','reused-prerequisites.json']:
 for m in json.loads((d/filename).read_text()):assert sha(Path(m['path']))==m['olean_sha256']
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');lib=Path('/workspace/pequalnp-proofs/lean/.lake/packages');env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,[O]+roots+[path/'prerequisites']+sorted(lib.glob('*/.lake/build/lib/lean'))))
cmd=[lean,'-j1','--root',S];records=[]
while set(rows)-lookup.keys():
 ready=[]
 for n in sorted(set(rows)-lookup.keys()):
  if set(re.findall(r'^import (ExactPlane\w+)',(S/(n+'.lean')).read_text(),re.M))<=lookup.keys():ready.append(n)
 assert ready
 for n in ready:
  f=S/(n+'.lean');o=O/(n+'.olean');deps=subprocess.check_output(cmd+['--deps',f],env=env,cwd=S,text=True).splitlines()
  for dd in map(Path,deps):
   assert dd.is_file()
   if dd.name.startswith('ExactPlane'):assert dd==lookup[dd.stem]
  log=subprocess.check_output(cmd+['-o',o,f.name],env=env,cwd=S,text=True);(D/(n+'.log')).write_text(log)
  ax=lambda t:[l for l in t.splitlines() if 'depends on axioms:' in l];aa=ax(log);assert aa==ax((S/'producer'/(n+'.log')).read_text())
  records.append(dict(module=n,source_sha256=sha(f),olean_sha256=sha(o),dependencies=deps,axioms=aa));lookup[n]=o;print(n,flush=True)
assert len(records)==13
demo=S/'ExactPlaneEagerSelectorExamples.lean';demo_log=subprocess.check_output(cmd+[demo.name],env=env,cwd=S,text=True);assert demo_log==(S/'producer/ExactPlaneEagerSelectorExamples.log').read_text()=='some 3\nsome 2\nfalse\nsome 3\nsome 3\n';(D/'demo.log').write_text(demo_log)
n='ExactPlaneEagerDecision';f=S/(n+'.lean');namespace=re.search(r'^namespace (\w+)',f.read_text(),re.M).group(1);q=R/'Audit.lean';q.write_text('import '+n+'\n#print axioms '+namespace+'.decide_with_basis\n');canon=subprocess.check_output([lean,'-j1',q],env=env,cwd=S,text=True);assert canon.strip().endswith('[propext, Classical.choice, Quot.sound]');(D/'final-axioms.log').write_text(canon)
(D/'statement.txt').write_text('theorem decide_with_basis'+f.read_text().split('theorem decide_with_basis',1)[1].split(' := by',1)[0]+'\n')
(D/'receipt.json').write_text(json.dumps(dict(commit=c,closure_manifest_sha256=sha(S/'EAGER-SOURCES.sha256'),closure_count=52,baseline_receipts=receipts,rehashed_reused_local_objects=39,new_modules=records,demo_source_sha256=sha(demo),demo=demo_log.splitlines(),axioms=canon.strip()),indent=2)+'\n')
