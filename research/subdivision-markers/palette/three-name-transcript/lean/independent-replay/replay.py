from pathlib import Path as P
import hashlib,json,os,subprocess,re,time
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip());s=w/'lean';fresh=w/'fresh-canonical';fresh.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock={'LEAN-SOURCES.sha256':'0cbfd79befce0a6aea58e21a77f61028506801db165bf5359c71a9a868dedd7b','semantic-manifest.sha256':'1c0e2b23de7ce3a3d1b68b87492fcd002533278d66302e27c11bc4986f50baeb','receipts/digests.txt':'a3319fd5810a9d70f00daa49fa326023e5b47e0ad6f7cf5735b2e27264ba1ceb'}
for f,h in lock.items():assert sha(s/f)==h
for f in ('LEAN-SOURCES.sha256','semantic-manifest.sha256'):
 for line in (s/f).read_text().splitlines():
  h,n=line.split()
  assert sha(s/n)==h,n
base=P('/workspace/scratch/three-name-transcript/lean')
objs={P(n).name:h for h,n in [l.split() for l in (s/'receipts/digests.txt').read_text().splitlines()]}
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
pkg=P('/workspace/pequalnp-proofs/lean/.lake/packages')
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env['LEAN_PATH']=':'.join(map(str,[fresh,*sorted(pkg.glob('*/.lake/build/lib/lean'))]))
def run(args,timeout=35):
 r=subprocess.run([lean,'-j1','--root='+str(base),*args],cwd=base,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
 assert r.returncode==0,(args,r.stdout)
 return r.stdout
done={}; ax=[]
for fn,h in objs.items():
 if not fn.endswith('.lean'):continue
 n=P(fn).stem;u=s/fn;p=fresh/(n+'.olean')
 assert sha(u)==h
 deps=run(['--deps',u]).splitlines()
 for path in map(P,deps):
  assert path.exists()
  if path.name.startswith('ThreeName'):assert path.resolve()==(fresh/path.name).resolve() and path.stem in done
 assert sha(base/fn)==h
 z=run(['-o',p,base/fn]); assert sha(base/fn)==h
 (d/(n+'.log')).write_text(z)
 gold=(s/'receipts'/(n+'.log')).read_text()
 assert z.replace(str(s)+'/',str(base)+'/')==gold and sha(p)==objs[p.name],(n,sha(p),z)
 ax+=re.findall(r"'([\w.]+)' depends on axioms",z)
 done[n]=dict(source=h,object=sha(p),rawlog=sha(d/(n+'.log')),producer_log=sha(s/'receipts'/(n+'.log')),deps=deps)
 print(n,flush=True)
assert len(done)==9
fixtures=re.findall(r'^theorem (\w+_fixture) ',(s/'ThreeNameFixtures.lean').read_text(),re.M)
allax=ax+['ThreeNameFixtures.'+f for f in fixtures]
probe=''.join('import '+n+'\n' for n in done)+''.join('#print axioms '+f+'\n' for f in allax)
(d/'axioms.lean').write_text(probe); z=run([d/'axioms.lean']);(d/'axioms.log').write_text(z)
assert len(z.splitlines())==len(allax) and 'sorryAx' not in z and '[propext, Classical.choice, Quot.sound]' in next(l for l in z.splitlines() if 'ThreeNameRejection.no_support' in l)
(d/'receipt.json').write_text(json.dumps(dict(commit='c6579c408d7e62745749685bcbe8f707f4c9eab9',locks=lock,lean=sha(lean),modules=done,axioms=allax,axioms_sha256=sha(d/'axioms.log'),controls_json=sha(w/'controls.json')),indent=2)+'\n')
print('PASS',len(done),len(allax),sha(d/'receipt.json'),flush=True)
