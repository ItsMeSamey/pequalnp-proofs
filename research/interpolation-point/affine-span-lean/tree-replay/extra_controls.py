from pathlib import Path as P
import os,subprocess
d=P(__file__).resolve().parent
w=P((d/'workdir').read_text().strip())
raw=P((d.parent/'review-plane-raw/workdir').read_text().strip())/'prerequisites'
lib=P('/workspace/pequalnp-proofs/lean/.lake/packages')
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env['LEAN_PATH']=':'.join(map(str,[w/'fresh',w/'prior',raw,*sorted(lib.glob('*/.lake/build/lib/lean'))]))
r=subprocess.run(['/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean','-j1',d/'controls.lean'],cwd=w,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(d/'controls.log').write_text(r.stdout)
assert r.returncode==0 and r.stdout.splitlines()==['none','some [0, 1, 2, 3]'],r.stdout
q=subprocess.run(['/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean','-j1',d/'extra_axioms.lean'],cwd=w,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(d/'extra_axioms.log').write_text(q.stdout)
assert q.returncode==0 and len(q.stdout.splitlines())==8 and all(x.endswith('[propext, Classical.choice, Quot.sound]') for x in q.stdout.splitlines()),q.stdout
