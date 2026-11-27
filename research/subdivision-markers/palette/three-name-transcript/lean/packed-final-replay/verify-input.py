from pathlib import Path as P
import sys,hashlib,subprocess,json
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip());p=w/'fixture/packed-fixture-producer'
out=w/'regen-sealed';out.mkdir(exist_ok=True)
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
subprocess.run([sys.executable,p/'generate.py',p/'pin-images.json',out/'ThreeNamePackedExample.lean'],check=True)
r={f.name:sha(f) for f in sorted(out.glob('*.lean'))}
assert len(r)==4 and all(sha(w/'fixture'/name)==h for name,h in r.items())
ctrl=subprocess.check_output([sys.executable,d/'controls.py',p/'pin-images.json'],text=True)
assert ctrl==(d/'controls.log').read_text()
inputs={f.name:sha(f) for f in [p/'generate.py',p/'pin-images.json',*sorted(p.glob('*.lean.in'))]}
raw=json.loads((p/'pin-images.json').read_text()); canon=json.dumps(raw['no']['certificate'],sort_keys=True,separators=(',',':')).encode()
(d/'inputs.json').write_text(json.dumps(dict(inputs=inputs,generated=r,certificate_sha256_canonical_json=hashlib.sha256(canon).hexdigest(),controls_sha256=sha(d/'controls.log')),indent=2)+'\n')
