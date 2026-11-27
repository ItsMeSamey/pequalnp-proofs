from pathlib import Path
import hashlib,subprocess,tempfile,os,json,re
D=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();c='1dad86ad9a420051ca30d84c2ffe9c35570a4ec6';rel='research/interpolation-point/affine-span-lean';R=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-small-chart-'));(D/'small-workdir').write_text(str(R)+'\n');S=R/rel;O=R/'fresh';O.mkdir()
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
rr=json.loads((D/'receipt.json').read_text());previous=Path((D/'workdir').read_text().strip())/'fresh';roots.insert(0,previous)
for m in rr['new_modules']:
 n=m['module'];obj=previous/(n+'.olean');assert sha(obj)==m['olean_sha256'] and rows[n]==m['source_sha256'];lookup[n]=obj
assert len(lookup)==71
env['LEAN_PATH']=os.pathsep.join(map(str,[O]+roots+[path/'prerequisites']+sorted(lib.glob('*/.lake/build/lib/lean'))))
inc=S/'SMALL-CHART-INCREMENT.sha256';assert sha(inc)=='8f9d68a160169625f01726db3323956a997e70b9fd1a6c476d21180c948b38e7'
for line in inc.read_text().splitlines():
 h,f=line.split();assert sha(S/f)==h;rows[Path(f).stem]=h
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
assert len(records)==2
demo=(D/'ExactPlaneSmallChartExamples.log').read_text();assert demo==(S/'producer/ExactPlaneSmallChartExamples.log').read_text() and '(some 3, false)' in demo
q=R/'AuditSmall.lean';q.write_text('import ExactPlaneSmallChartFallback\n#print axioms ExactPlaneSmallChartFallback.solve_iff\n#print axioms ExactPlaneSmallChartFallback.witness\n');ca=subprocess.check_output([lean,'-j1',q],env=env,cwd=S,text=True);assert ca.count('[propext, Classical.choice, Quot.sound]')==2;(D/'small-axioms.log').write_text(ca)
(D/'small-receipt.json').write_text(json.dumps(dict(commit=c,increment_sha256=sha(inc),field_receipt_sha256=sha(D/'receipt.json'),new_modules=records,demo=demo.strip(),axioms=ca.splitlines()),indent=2)+'\n')
