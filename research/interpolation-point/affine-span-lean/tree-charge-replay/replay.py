from pathlib import Path as P
import hashlib,json,os,subprocess
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip()); td=d.parent/'review-plane-tree'; tr=td/'receipt.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(tr)=='f8e223ae10c7c45aaec284e6d1e44b00b3a06c316b100f65cb51c3d314811402'
r=json.loads(tr.read_text());t=P(r['workdir']);known={n:P(p) for n,(p,h) in r['reused'].items()}
for n,(p,h) in r['reused'].items():assert sha(P(p))==h
for x in r['new_modules']:
 n=x['module'];p=t/'fresh'/(n+'.olean');assert sha(p)==x['olean_sha256'];known[n]=p
for n,h in r['closure'].items():assert sha(t/(n+'.lean'))==h
f=w/'fresh';f.mkdir(); raw=P((d.parent/'review-plane-raw/workdir').read_text().strip())/'prerequisites';pkg=P('/workspace/pequalnp-proofs/lean/.lake/packages')
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['LEAN_PATH']=':'.join(map(str,[f,t/'fresh',t/'prior',raw,*sorted(pkg.glob('*/.lake/build/lib/lean'))]))
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
assert sha(lean)==r['compiler']
def run(args):
 q=subprocess.run([lean,'-j1',*args],env=env,cwd=w,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);assert q.returncode==0,q.stdout
 return q.stdout
n='ExactPlaneWedgeFusedCharges';s=n+'.lean';o=f/(n+'.olean');e=w/'tree-charge-producer'/(n+'.sha256')
g={P(p).suffix:h for h,p in [x.split() for x in e.read_text().splitlines()]}
assert sha(w/s)==g['.lean']=='b69c5e8ce61876cbcca6f6a7b8a0aed533bae866996ac250a450edce0999fe54'
deps=run(['--deps',s]).splitlines()
for p in map(P,deps):
 if p.name.startswith('ExactPlane'):assert p.resolve()==known[p.stem].resolve()
z=run(['-o',o,s]);(d/(n+'.log')).write_text(z);assert sha(o)==g['.olean'] and sha(d/(n+'.log'))==g['.log']
probe=d/'axioms.lean';probe.write_text('import '+n+'\n#print axioms '+n+'.callbacks\n#print axioms '+n+'.same_count\n#print axioms '+n+'.fused_cap\n')
z=run([probe]);(d/'axioms.log').write_text(z);assert len(z.splitlines())==3 and all('sorryAx' not in x for x in z.splitlines())
(d/'receipt.json').write_text(json.dumps(dict(commit='40a5fb5160a2211b7cbc3c2548ba873135012c06',baseline=sha(tr),files=g,deps=deps,axioms=sha(d/'axioms.log')),indent=2)+'\n');print(sha(d/'receipt.json'))
