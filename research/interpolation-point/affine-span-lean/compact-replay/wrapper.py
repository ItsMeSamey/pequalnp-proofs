from pathlib import Path
import hashlib,subprocess,tempfile,os,json
D=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();c='49bc564ebf84539cd39704f1453ba84d9d5eb77a';r=json.loads((D/'receipt.json').read_text());R=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-compact-'));S=R/r['rel'];O=R/'fresh';O.mkdir()
p=subprocess.Popen(['git','-C','/workspace/pnp-research','archive',c,r['rel']],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',R],stdin=p.stdout,check=True);assert p.wait()==0
assert sha(S/'COMPACT-SOURCES.sha256')=='07739fc01f9db17a9326cf23a9f30e088feb85b395b8a320faf3be2112fb673d'
roots=[];lookup={}
for d in [D,D.parent/'review-plane-raw-small',D.parent/'review-plane-raw']:
 rr=json.loads((d/'receipt.json').read_text());path=Path((d/'workdir').read_text().strip());roots.append(path/'fresh')
 for m in rr['modules']:
  n=m['module'];obj=path/'fresh'/(n+'.olean');assert sha(obj)==m['olean_sha256'] and sha(S/(n+'.lean'))==m['source_sha256'];lookup[n]=obj
rows=[l.split() for l in (S/'COMPACT-SOURCES.sha256').read_text().splitlines()];assert len(rows)==41
for h,f in rows:assert sha(S/f)==h
assert {Path(f).stem for h,f in rows}-lookup.keys()=={'ExactPlaneCompactDecision'}
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');lib=Path('/workspace/pequalnp-proofs/lean/.lake/packages');env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,[O]+roots+[path/'prerequisites']+sorted(lib.glob('*/.lake/build/lib/lean'))))
f=S/'ExactPlaneCompactDecision.lean';o=O/'ExactPlaneCompactDecision.olean';cmd=[lean,'-j1','--root',S];deps=subprocess.check_output(cmd+['--deps',f],env=env,cwd=S,text=True).splitlines();assert [p for p in deps if Path(p).name.startswith('ExactPlane')]==[str(lookup['ExactPlaneExecutableCompression'])]
log=subprocess.check_output(cmd+['-o',o,f.name],env=env,cwd=S,text=True);(D/'ExactPlaneCompactDecision.log').write_text(log);assert log==(S/'producer/ExactPlaneCompactDecision.log').read_text()
probe=R/'FinalAudit.lean';probe.write_text('import ExactPlaneCompactDecision\n#print axioms ExactPlaneExecutableSelector.compact_decision\n');canon=subprocess.check_output([lean,'-j1',probe],env=env,cwd=S,text=True);assert canon.strip()=="'ExactPlaneExecutableSelector.compact_decision' depends on axioms: [propext, Classical.choice, Quot.sound]";(D/'final-axioms.log').write_text(canon)
(D/'compact-statement.txt').write_text('theorem compact_decision'+f.read_text().split('theorem compact_decision',1)[1].split(' := by',1)[0]+'\n')
(D/'compact-receipt.json').write_text(json.dumps(dict(commit=c,closure_sources=41,closure_manifest_sha256=sha(S/'COMPACT-SOURCES.sha256'),preceding_receipt_sha256=sha(D/'receipt.json'),final_source_sha256=sha(f),final_object_sha256=sha(o),final_deps=deps,axioms=canon.strip(),demo=r['demo']),indent=2)+'\n')
