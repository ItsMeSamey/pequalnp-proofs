from pathlib import Path
import csv, hashlib, json, os, subprocess
D=Path(__file__).resolve().parent
root=Path((D/'workdir').read_text().strip());lock=json.loads((D/'source-lock.json').read_text());bundle=root/lock['rel']
sha=lambda b: hashlib.sha256(b).hexdigest()
overlay=root/'prerequisites';overlay.mkdir()
base=Path('/dev/shm/gcycle-t2/mathlib')
lake=Path('/workspace/pequalnp-proofs/lean');pkgs=lake/'.lake/packages';math=pkgs/'mathlib'
lean=Path('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
pins={p['name']:p['rev'] for p in json.loads((lake/'lake-manifest.json').read_text())['packages']}
assert sha((lake/'lake-manifest.json').read_bytes())=='d0af863cde532caaef1b1bee0d63ec47100208e33e488309cb80abc88b8f1509'
assert sha(lean.read_bytes())=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
mods=['Mathlib.LinearAlgebra.AffineSpace.Defs','Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs']
skip=[Path(m.replace('.','/')) for m in mods]
def link_siblings(r):
 d=overlay/r;d.mkdir(exist_ok=True)
 for x in (base/r).iterdir():
  z=x.relative_to(base)
  if any(z.parent==p.parent and (z.name==p.name or z.name.startswith(p.name+'.')) for p in skip):continue
  if any(p.is_relative_to(z) for p in skip):link_siblings(z)
  else:(overlay/z).symlink_to(x)
link_siblings(Path('.'))
libs=[x for x in sorted(pkgs.glob('*/.lake/build/lib/lean')) if x.is_dir()]
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=os.pathsep.join(map(str,[overlay]+libs))
src=root/'mathlib-source';src.mkdir();results=[]
for i,m in enumerate(mods):
 f=Path(m.replace('.','/')+'.lean');source=src/f;source.parent.mkdir(parents=True,exist_ok=True)
 source.write_bytes(subprocess.check_output(['git','-C',math,'show',pins['mathlib']+':'+str(f)]))
 blob=subprocess.check_output(['git','-C',math,'rev-parse',pins['mathlib']+':'+str(f)],text=True).strip()
 o=(overlay/f).with_suffix('.olean');assert not o.exists()
 cmd=[str(lean),'-j1','--root',str(src)];deps=subprocess.check_output(cmd+['--deps',str(source)],env=env,cwd=src,text=True).splitlines()
 assert all(Path(p).is_file() for p in deps)
 if i:assert str(overlay/'Mathlib/LinearAlgebra/AffineSpace/Defs.olean') in deps
 subprocess.run(cmd+['-o',str(o),str(source)],env=env,cwd=src,check=True)
 results.append(dict(module=m,git_revision=pins['mathlib'],git_blob=blob,source_sha256=sha(source.read_bytes()),olean_sha256=sha(o.read_bytes()),path=str(o),deps=deps))
(D/'prerequisites.json').write_text(json.dumps(results,indent=2)+'\n')
