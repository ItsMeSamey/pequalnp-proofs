from pathlib import Path
import json,subprocess,hashlib,re,os
D=Path(__file__).resolve().parent;R=Path((D/'workdir').read_text().strip()); lock=json.loads((D/'source-lock.json').read_text());src=R/lock['rel'];out=R/'fresh';out.mkdir()
pkgs=Path('/workspace/pequalnp-proofs/lean/.lake/packages');lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');libs=[out,R/'prerequisites']+sorted(pkgs.glob('*/.lake/build/lib/lean'))
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,libs))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['ExactPlaneFieldCard', 'ExactPlaneFieldSampler', 'ExactPlaneSubsetPolynomial', 'ExactPlaneAffineSparse', 'ExactPlaneAffineSubstitution', 'ExactPlaneAffineSpanHit', 'ExactPlaneTwoBitLookup', 'ExactPlaneActivationSlice', 'ExactPlaneDeterminant', 'ExactPlaneActiveDeterminant', 'ExactPlaneLookupDeterminant', 'ExactPlaneSamplerSpan', 'ExactPlaneActiveReadSpan', 'ExactPlaneSamplerRank', 'ExactPlaneConcreteSampler', 'ExactPlaneOntoReadSpan', 'ExactPlaneCanonicalReadSpan']
assert {x.stem for x in src.glob('*.lean')}==set(mods)
pins={p['name']:p['rev'] for p in json.loads((pkgs.parent.parent/'lake-manifest.json').read_text())['packages']}
for pkg,h in pins.items(): assert subprocess.check_output(['git','-C',pkgs/pkg,'rev-parse','HEAD'],text=True).strip()==h
pre=json.loads((D/'reused-prerequisites.json').read_text())+json.loads((D/'prerequisites.json').read_text()); records=[];comp=[]
for line in [l for f in (src/'producer').glob('*prerequisites.sha256') for l in f.read_text().splitlines()]:
 h,p=line.split();matches=[v for v in pre if p.endswith('/'+v['module'].replace('.','/')+Path(p).suffix)]
 assert len(matches)==1 and matches[0]['source_sha256' if p.endswith('.lean') else 'olean_sha256']==h
for m in mods:
 f=src/(m+'.lean');o=out/(m+'.olean');cmd=[lean,'-j1','--root',src]
 deps=subprocess.check_output(cmd+['--deps',f],env=env,cwd=src,text=True).splitlines()
 direct=set(re.findall(r'^import (ExactPlane\w+)',f.read_text(),re.M));fresh={Path(x).stem for x in deps if Path(x).resolve().is_relative_to(out)}
 assert fresh==direct and direct<=set(comp)
 for dep in map(Path,deps):
  assert dep.is_file() and (any(dep.is_relative_to(x) for x in libs) or dep.is_relative_to(lean.parent.parent))
  if dep.stem in mods:assert dep.resolve().is_relative_to(out)
 if m=='ExactPlaneAffineSpanHit':assert Path(pre[1]['path']).resolve() in [Path(x).resolve() for x in deps]
 run=subprocess.run(cmd+['-o',o,f],env=env,cwd=src,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(D/(m+'.log')).write_text(run.stdout)
 assert run.returncode==0,(m,run.stdout)
 reports=[l for l in run.stdout.splitlines() if 'depends on axioms:' in l]
 expected=[l for l in (src/'producer'/(m+'.log')).read_text().splitlines() if 'depends on axioms:' in l]
 assert reports==expected
 if m=='ExactPlaneCanonicalReadSpan': assert reports==["'ExactPlaneLookupDeterminant.universal_read_seed' depends on axioms: [propext, Classical.choice, Quot.sound]"]
 records.append(dict(module=m,source_sha256=sha(f),olean_sha256=sha(o),deps=deps,axioms=reports));comp.append(m);print(m,flush=True)
assert len(list(out.glob('*.olean')))==17
(D/'receipt.json').write_text(json.dumps(dict(**lock,modules=records,pinned_packages=pins,lean_sha256=sha(lean),prerequisites_sha256=sha(D/'prerequisites.json')),indent=2)+'\n')
