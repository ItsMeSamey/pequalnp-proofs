from pathlib import Path
from hashlib import sha256
import os, csv, subprocess, json, sys
resume='--resume' in sys.argv[1:]
from datetime import datetime, timezone
D=Path(__file__).resolve().parent
R=Path((D/'workdir').read_text().strip())
lock=json.loads((D/'source-lock.json').read_text()); rel=lock['rel']
P=R/rel; src=P/'sources'; out=R/'fresh'; out.mkdir(exist_ok=resume)
if not resume: assert not list(out.iterdir())
leanproject=Path('/workspace/pequalnp-proofs/lean')
pkgs=leanproject/'.lake/packages'
math=Path('/dev/shm/gcycle-t2/mathlib')
paths=[out,math]+[lib for lib in sorted(pkgs.glob('*/.lake/build/lib/lean')) if lib.is_dir()]
assert set(x.name for x in math.iterdir())=={'Mathlib'}
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
env={k:v for k,v in os.environ.items() if not k.startswith('LEAN') and not k.startswith('LAKE')}
env['LEAN_PATH']=os.pathsep.join(str(x) for x in paths)
def digest(x):return sha256(x.read_bytes()).hexdigest()
def run(cmd):return subprocess.check_output(cmd,text=True,env=env,cwd=src).strip()
def stamp():return datetime.now(timezone.utc).isoformat()
m=P/'ThresholdPublicSharp-manifest.tsv'; rows=list(csv.DictReader(m.open(),delimiter='\t'))
names={r['module'] for r in rows}; seen=set()
assert len(rows)==len(names)==len(list(src.rglob('*.lean')))==109
assert sum(x.startswith('PEqualNP.') for x in names)==6
for r in rows:
 name=r['module']; f=P/r['source_path']
 assert f.relative_to(src).as_posix()==name.replace('.','/')+'.lean'
 assert digest(f)==r['source_sha256']
 for where in paths[1:]:
  assert not (where/(name.replace('.','/')+'.olean')).exists(),(where,name)
 for dep in r['direct_imports'].split():
  assert dep not in names or dep in seen,(name,dep)
 seen.add(name)
revisions={p.name:subprocess.check_output(['git','-C',p,'rev-parse','HEAD'],text=True).strip() for p in pkgs.iterdir() if (p/'.git').exists()}
anchor=lock['commit']
assert digest(m)==lock['manifest_sha256']
meta=dict(commit=anchor,tree=lock['tree'],version=run([lean,'--version']),manifest_sha256=digest(m),lake_manifest_sha256=digest(leanproject/'lake-manifest.json'),lean_sha256=digest(lean),paths=list(map(str,paths)),source_count=109,package_revisions=revisions,start=stamp())
if resume:
 old=json.loads((D/'environment.json').read_text())
 assert {k:v for k,v in meta.items() if k!='start'}=={k:v for k,v in old.items() if k!='start'}
 meta=old
 completed=list(csv.DictReader((D/'objects.tsv').open(),delimiter='\t'))
 assert [r['module'] for r in completed]==[r['module'] for r in rows[:len(completed)]]
 for r in completed: assert digest(out/(r['module'].replace('.','/')+'.olean'))==r['olean_sha256']
 assert len(list(out.rglob('*.olean')))==len(completed)
 outputs=open(D/'objects.tsv','a',buffering=1);resolution=open(D/'resolved.tsv','a',buffering=1)
else:
 completed=[]
 (D/'environment.json').write_text(json.dumps(meta,indent=2)+'\n')
 (D/'kernel.log').write_text('')
 outputs=open(D/'objects.tsv','w',buffering=1);print('module\tsource_sha256\tolean_sha256\tfinished_utc',file=outputs)
 resolution=open(D/'resolved.tsv','w',buffering=1);print('caller\tresolved_dependency',file=resolution)
for j,r in enumerate(rows,1):
 if j<=len(completed):continue
 name=r['module']; f=P/r['source_path']; o=out/(name.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
 deps=run([lean,'--root',str(src),'--deps',str(f)]).splitlines()
 reported=set()
 for line in deps:
  resolved=Path(line).resolve()
  assert resolved.is_file(),(name,line)
  lex=Path(line)
  assert any(lex.is_relative_to(x) for x in paths) or lex.is_relative_to(lean.parent.parent),(name,lex)
  if not resolved.is_relative_to(out) and not lex.is_relative_to(lean.parent.parent):
   x=next(x for x in paths[1:] if lex.is_relative_to(x))
   modulefile=lex.relative_to(x)
   assert modulefile.parts[0] in {'Mathlib','Batteries','Lean','Qq','Aesop','ProofWidgets','Plausible','ImportGraph','LeanSearchClient','Init'},(name,modulefile)
   assert any((root/modulefile).exists() and (root/modulefile).resolve()==resolved for root in paths[1:]),(name,resolved)
  if resolved.is_relative_to(out):
   reported.add(resolved.relative_to(out).as_posix().removesuffix('.olean').replace('/','.'))
  print(name,line,sep='\t',file=resolution)
 assert reported=={d for d in r['direct_imports'].split() if d in names},(name,reported)
 print(f'{j}/109 {name}',flush=True)
 p=subprocess.run([lean,'-j1','--root',str(src),'-o',str(o),str(f)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env,cwd=src)
 with open(D/'kernel.log','a') as log:print(f'[{j}/109 {name}]\n'+p.stdout,file=log)
 if p.returncode:sys.exit(p.returncode)
 print(name,digest(f),digest(o),stamp(),sep='\t',file=outputs)
 if j==109:
  expected=(P/'axioms.log').read_text().splitlines()
  assert len(expected)==3
  assert all(s in p.stdout.splitlines() for s in expected),p.stdout
  (D/'axioms.log').write_text('\n'.join(expected)+'\n')
outputs.close();resolution.close()
assert len(list(out.rglob('*.olean')))==109
meta.update(finish=stamp(),outputs_sha256=digest(D/'objects.tsv'),resolution_sha256=digest(D/'resolved.tsv'),axioms_sha256=digest(D/'axioms.log'))
(D/'receipt.json').write_text(json.dumps(meta,indent=2)+'\n');print('VERIFIED',flush=True)
