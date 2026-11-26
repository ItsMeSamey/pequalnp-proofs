from pathlib import Path
import json,subprocess,hashlib,tempfile,os
D=Path(__file__).resolve().parent;R=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-23368-'));(D/'workdir').write_text(str(R)+'\n')
commit='79b1939e0586292c4a3e17332caaa666b213b364';rel='research/one-hot-circuits/mask-818815';repo='/workspace/pnp-research'
p=subprocess.Popen(['git','-C',repo,'archive',commit,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',R],stdin=p.stdout,check=True);assert p.wait()==0
s=R/rel;o=R/'fresh';o.mkdir();project=Path('/workspace/pequalnp-proofs/lean');lib=project/'.lake/build/lib/lean';libs=[o,Path('/dev/shm/gcycle-t2/mathlib'),lib]+sorted((project/'.lake/packages').glob('*/.lake/build/lib/lean'))
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean');env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,libs));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();mods=['Mask818815Upper','L_meta_23368']; rec=[]
for m in mods:
 f=s/(m+'.lean');obj=o/(m+'.olean');pins=(s/(m+'.sha256')).read_text().splitlines();assert sha(f)==pins[0].split()[0]
 cmd=[lean,'-j1','--root',s];dependencies=subprocess.check_output(cmd+['--deps',f],env=env,cwd=s,text=True).splitlines();assert str(lib/'PEqualNP/Defs.olean') in dependencies
 assert not any((base/(m+'.olean')).exists() for base in libs[1:])
 with (D/(m+'.log')).open('w') as log:subprocess.run(cmd+['-o',obj,f.name],env=env,cwd=s,stdout=log,stderr=subprocess.STDOUT,check=True)
 assert obj.is_file()
 rec.append(dict(module=m,source_sha256=sha(f),object_sha256=sha(obj),producer_object_sha256=pins[1].split()[0],dependencies=dependencies))
 print(m,flush=True)
a=s/'Axioms23368.lean';assert str(o/'L_meta_23368.olean') in subprocess.check_output(cmd+['--deps',a],env=env,cwd=s,text=True).splitlines()
log=subprocess.check_output(cmd+[a],env=env,cwd=s,text=True);assert log==(s/'Axioms23368.log').read_text();(D/'axioms-lower.log').write_text(log)
b=s/'AuditUpper.lean';b.write_text('import Mask818815Upper\n#print axioms Mask818815.upper\n');assert str(o/'Mask818815Upper.olean') in subprocess.check_output(cmd+['--deps',b],env=env,cwd=s,text=True).splitlines()
u=subprocess.check_output(cmd+[b],env=env,cwd=s,text=True);(D/'axioms-upper.log').write_text(u)
assert 'sorryAx' not in u and 'Mask818815.upper' in u
receipt=dict(commit=commit,tree=subprocess.check_output(['git','-C',repo,'rev-parse',commit+':'+rel],text=True).strip(),project_commit=subprocess.check_output(['git','-C',project,'rev-parse','HEAD'],text=True).strip(),defs_source_sha256=sha(project/'PEqualNP/Defs.lean'),defs_object_sha256=sha(lib/'PEqualNP/Defs.olean'),lean_sha256=sha(lean),lake_sha256=sha(project/'lake-manifest.json'),modules=rec,lower_axioms=log.strip(),upper_axioms=u.strip())
(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
