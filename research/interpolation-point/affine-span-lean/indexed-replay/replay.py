from pathlib import Path as P
import hashlib,json,os,subprocess,re
d=P(__file__).resolve().parent
w=P((d/'workdir').read_text().strip())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def manifest(p):return {P(n).stem:h for h,n in (s.split() for s in p.read_text().splitlines())}
a=manifest(w/'INDEXED-SOURCES.sha256'); inc=manifest(w/'INDEXED-INCREMENT.sha256')
assert len(a)==73 and len(inc)==20
locks={'INDEXED-SOURCES.sha256':'09d285b8bf8bb5259a282d6d5c79c788b744836803cbe904984a42cda468ff53','INDEXED-INCREMENT.sha256':'ad0743910e0cf4cb21d8cce5983d93dccaa2e1f807d1e6279ac1d670a51eef05','producer/indexed-full.sha256':'0f202872421174c67b47354adb81b0b03a33ee7034d8f3055da409c3edcd40b2','producer/indexed-increment.sha256':'d56e7ebde6e1f0db14bbb3e5541b5b0fbefd0343875b1275c9b249e324abfd72'}
assert all(sha(w/k)==v for k,v in locks.items()) and manifest(w/'producer/indexed-full.sha256')==a and manifest(w/'producer/indexed-increment.sha256')==inc
assert all(sha(w/(n+'.lean'))==h for n,h in a.items())
cp=d.parent/'review-plane-charges/receipt.json'
assert sha(cp)=='93baeeacc345ead358357cee7fa897b6fba552b1dae6ce1c4b5b458dec34b978'
c=json.loads(cp.read_text()); old=c['reused']|{r['module']:[str(P(c['workdir'])/'fresh'/(r['module']+'.olean')),r['olean_sha256']] for r in c['new_modules']}
fresh=w/'fresh';prior=w/'prior';fresh.mkdir();prior.mkdir()
known={}; reused={}
for n in a.keys()-inc.keys():
 p,h=old[n];p=P(p);assert c['closure'][n]==a[n] and sha(p)==h
 (prior/p.name).symlink_to(p);known[n]=p;reused[n]=[str(p),h]
raw=d.parent/'review-plane-raw'
overlay=P((raw/'workdir').read_text().strip())/'prerequisites'
pre=[]
for f in ['prerequisites.json','reused-prerequisites.json']:
 for r in json.loads((raw/f).read_text()):
  p=P(r['path']); assert sha(p)==r['olean_sha256']; pre.append(r)
lib=P('/workspace/pequalnp-proofs/lean/.lake/packages')
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
assert sha(lean)=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env['LEAN_PATH']=':'.join(map(str,[fresh,prior,overlay,*sorted(lib.glob('*/.lake/build/lib/lean'))]))
def run(args):
 r=subprocess.run([lean,'-j1',*args],cwd=w,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 assert not r.returncode,r.stdout
 return r.stdout
build=[]; axs=[]
while set(inc)-set(known):
 n=next(n for n in inc if n not in known and set(re.findall(r'^import (ExactPlane\w+)',(w/(n+'.lean')).read_text(),re.M))<=known.keys())
 fn=n+'.lean';obj=fresh/(n+'.olean')
 deps=run(['--deps',fn]).splitlines()
 for p in map(P,deps):
  assert p.exists()
  if p.name.startswith('ExactPlane'):assert known[p.stem].resolve()==p.resolve()
 log=run(['-o',obj,fn]); (d/(n+'.log')).write_text(log)
 prod={P(p).suffix:h for h,p in (s.split() for s in (w/'producer'/(n+'.sha256')).read_text().splitlines())}
 assert prod=={'.lean':inc[n],'.olean':sha(obj),'.log':sha(d/(n+'.log'))},(n,prod,sha(obj),log)
 assert log==(w/'producer'/(n+'.log')).read_text()
 axs.extend(re.findall(r"'([A-Za-z0-9_\.]+)' depends on axioms",log))
 build.append(dict(module=n,source_sha256=inc[n],olean_sha256=sha(obj),log_sha256=prod['.log'],deps=deps));known[n]=obj
 print(n,flush=True)
probe=''.join('import '+n+'\n' for n in inc)+''.join('#print axioms '+n+'\n' for n in axs)
(d/'axioms.lean').write_text(probe); z=run([d/'axioms.lean']); (d/'axioms.log').write_text(z)
assert len(z.splitlines())==len(axs) and all('sorryAx' not in l and all(x in ['propext','Classical.choice','Quot.sound'] for x in l.split('[')[1].split(']')[0].split(', ')) for l in z.splitlines())
(d/'receipt.json').write_text(json.dumps(dict(commit='fd7787aa7583a82fb9c735f290b53dd3a2a54190',locks=locks,compiler=sha(lean),workdir=str(w),closure=a,reused=reused,prior_receipt=sha(cp),new_modules=build,prerequisites=pre,axioms=axs,axioms_sha256=sha(d/'axioms.log')),indent=2)+'\n')
print('PASS',len(build),len(reused),len(axs),sha(d/'receipt.json'),flush=True)
