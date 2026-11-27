from pathlib import Path as P
import hashlib,json,os,subprocess,re
d=P(__file__).resolve().parent
w=P((d/'workdir').read_text().strip())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def manifest(p):return {P(n).stem:h for h,n in (s.split() for s in p.read_text().splitlines())}
a=manifest(w/'TREE-SOURCES.sha256'); inc=manifest(w/'TREE-INCREMENT.sha256')
assert len(a)==98 and len(inc)==39
locks={'TREE-SOURCES.sha256':'9643016324a09bced2ec51ec19dbc4d1aa7651bcb61d4006295749a9f195bc28','TREE-INCREMENT.sha256':'a87f5bc83cab6a71c87800af445ed9431d56ec8649c6042e3d8b108488955e58','producer/tree-full.sha256':'a476e5a1ae661356eb68487fa79f46bb538f221879f21bc834043b156168d98b','producer/tree-increment.sha256':'b89f678c1df60543127b188dd43bc9a3d9a3c3c83fa19a75bafa01ead76285c1'}
assert all(sha(w/k)==v for k,v in locks.items()) and manifest(w/'producer/tree-full.sha256')==a and manifest(w/'producer/tree-increment.sha256')==inc
assert all(sha(w/(n+'.lean'))==h for n,h in a.items())
cp=d.parent/'review-plane-charges/receipt.json'
assert sha(cp)=='93baeeacc345ead358357cee7fa897b6fba552b1dae6ce1c4b5b458dec34b978'
c=json.loads(cp.read_text()); old=c['reused']|{r['module']:[str(P(c['workdir'])/'fresh'/(r['module']+'.olean')),r['olean_sha256']] for r in c['new_modules']}
ip=d.parent/'review-plane-indexed/receipt.json'
assert sha(ip)=='a090e95a9d580536accffdf66f64b5fa0b8bb70c135100bf8d9ec443998027b0'
i=json.loads(ip.read_text())
old.update(i['reused']); old.update({r['module']:[str(P(i['workdir'])/'fresh'/(r['module']+'.olean')),r['olean_sha256']] for r in i['new_modules']})
c['closure'].update(i['closure'])
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
 if len(build)==15:
  import time
  (d/'checkpoint').touch()
  while not (d/'continue').exists():time.sleep(1)
probe=''.join('import '+n+'\n' for n in inc)+''.join('#print axioms '+n+'\n' for n in axs)
(d/'axioms.lean').write_text(probe); z=run([d/'axioms.lean']); (d/'axioms.log').write_text(z)
assert len(z.splitlines())==len(axs) and all('sorryAx' not in l and all(x in ['propext','Classical.choice','Quot.sound'] for x in l.split('[')[1].split(']')[0].split(', ')) for l in z.splitlines())
(d/'receipt.json').write_text(json.dumps(dict(commit='ec21602f9f090c2aeb9b7d60268bbcbb3c7c0775',locks=locks,compiler=sha(lean),workdir=str(w),closure=a,reused=reused,prior_receipts=[sha(cp),sha(ip)],new_modules=build,prerequisites=pre,axioms=axs,axioms_sha256=sha(d/'axioms.log')),indent=2)+'\n')
print('PASS',len(build),len(reused),len(axs),sha(d/'receipt.json'),flush=True)
