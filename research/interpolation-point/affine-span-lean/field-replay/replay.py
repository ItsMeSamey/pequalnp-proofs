from pathlib import Path
import hashlib,subprocess,tempfile,os,json,re
D=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();c='0b365939376ac03c0c2d9d4bb7fb5e2a3a732523';rel='research/interpolation-point/affine-span-lean';R=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-field-'));(D/'workdir').write_text(str(R)+'\n');S=R/rel;O=R/'fresh';O.mkdir()
p=subprocess.Popen(['git','-C','/workspace/pnp-research','archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',R],stdin=p.stdout,check=True);assert p.wait()==0
assert sha(S/'FIELD-SOURCES.sha256')=='9bee2b01993099a0c1569c859df166aed307e6521e3367570b46d4dac1f7328e'
rows={Path(l.split()[1]).stem:l.split()[0] for l in (S/'FIELD-SOURCES.sha256').read_text().splitlines()};assert len(rows)==71
for name,h in rows.items():assert sha(S/(name+'.lean'))==h
roots=[];lookup={};receipts={}
for folder,hh in [('review-plane-executable','c3ea13a5cb43e45e505d3b00fbf95eb881b4a858bb55e0d4539ad27e002d7bcf'),('review-plane-raw-small','26fc4fe5e3eb164a499abfb41ded15366195c79defa464ea63bc5abfc06581ea'),('review-plane-raw','91b70c85dc73613e9f3feaf04fa82ca46ca2cebb977020b5fde14b7df9a93794')]:
 d=D.parent/folder;assert sha(d/'receipt.json')==hh;receipts[folder]=hh;rr=json.loads((d/'receipt.json').read_text());path=Path((d/'workdir').read_text().strip());roots.append(path/'fresh')
 for m in rr['modules']:
  n=m['module']
  if n in rows:
   obj=path/'fresh'/(n+'.olean');assert sha(obj)==m['olean_sha256'] and rows[n]==m['source_sha256'];lookup[n]=obj
gd=D.parent/'review-plane-gaussian';gc=json.loads((gd/'receipt.json').read_text());assert sha(gd/'receipt.json')=='e5044cd45b4e0a39472c77bff59f451eacb7f3b3f58e3e25a0c2003ca61b3f93';receipts['review-plane-gaussian']=sha(gd/'receipt.json');gout=Path((gd/'workdir').read_text().strip())/'fresh';roots.insert(0,gout)
for m in gc['new_modules']:
 n=m['module']
 if n in rows:
  obj=gout/(n+'.olean');assert sha(obj)==m['olean_sha256'] and rows[n]==m['source_sha256'];lookup[n]=obj
assert len(lookup)==50,len(lookup)
prod=S/'producer/field-increment.sha256';assert sha(prod)=='77197c9bd8be1baf97f8b967c92c541cd7e6c4db14d940eb469e6db74abd7e0d';assert set(rows)-lookup.keys()=={Path(l.split()[1]).stem for l in prod.read_text().splitlines()}
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
assert len(records)==21
demo=S/'ExactPlaneGeneratedExamples.lean';demo_log=(D/'ExactPlaneGeneratedExamples.log').read_text();assert demo_log==(S/'producer/ExactPlaneGeneratedExamples.log').read_text();(D/'demo.log').write_text(demo_log)
n='ExactPlaneDeficitSolver';f=S/(n+'.lean');q=R/'Audit.lean';q.write_text('import '+n+'\n'+''.join('#print axioms '+n+'.'+t+'\n' for t in ['packed_iff','solve_iff','witness']));canon=subprocess.check_output([lean,'-j1',q],env=env,cwd=S,text=True);assert canon.count('[propext, Classical.choice, Quot.sound]')==3;(D/'final-axioms.log').write_text(canon)
(D/'statements.lean.txt').write_text(f.read_text())
(D/'receipt.json').write_text(json.dumps(dict(commit=c,closure_manifest_sha256=sha(S/'FIELD-SOURCES.sha256'),closure_count=71,baseline_receipts=receipts,rehashed_reused_local_objects=50,new_modules=records,demo_source_sha256=sha(demo),demo=demo_log.splitlines(),axioms=canon.splitlines()),indent=2)+'\n')
