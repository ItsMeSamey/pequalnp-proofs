from pathlib import Path
import tempfile,subprocess,json,hashlib,os
D=Path(__file__).resolve().parent;pre=D.parent/'review-exact-plane-clean';old=Path((pre/'workdir').read_text().strip())
root=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-plane-sampler-'));c='eaf83f5e22d12b9d1e3fef3c9ebaa952b6ecea02';rel='research/interpolation-point/affine-span-lean';repo='/workspace/pnp-research'
p=subprocess.Popen(['git','-C',repo,'archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',root],stdin=p.stdout,check=True);assert p.wait()==0
s=root/rel;h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ms='41e3b6a79f9be4dc6bef89aff44ee56306dd850207d0773b4b5c3ca44b8bec76';assert h(s/'SHA256SUMS')==ms
for l in (s/'SHA256SUMS').read_text().splitlines():
 dig,path=l.split(); assert h(s/path)==dig
assert h(pre/'prerequisites.json')=='b99b2eeff9b445978b2b3d9275a58e0ced195176b444ee6294ec4f0329b6c4ef'
for x in json.loads((pre/'prerequisites.json').read_text()):
 assert h(Path(x['path']))==x['olean_sha256'] and h(old/'mathlib-source'/(x['module'].replace('.','/')+'.lean'))==x['source_sha256']

(D/'reused-prerequisites.json').write_bytes((pre/'prerequisites.json').read_bytes());(D/'workdir').write_text(str(root)+'\n')
(D/'source-lock.json').write_text(json.dumps(dict(commit=c,rel=rel,tree=subprocess.check_output(['git','-C',repo,'rev-parse',c+':'+rel],text=True).strip(),manifest_sha256=ms,dependency_receipt_sha256=h(pre/'receipt.json')),indent=2)+'\n')
