from pathlib import Path
import tempfile,subprocess,json,hashlib,os
D=Path(__file__).resolve().parent;pre=D.parent/'review-exact-plane-clean';old=Path((pre/'workdir').read_text().strip())
root=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-plane-determinant-'));c='e12cf1c12083b617248880d3479ae5ed13fd5c29';rel='research/interpolation-point/affine-span-lean';repo='/workspace/pnp-research'
p=subprocess.Popen(['git','-C',repo,'archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',root],stdin=p.stdout,check=True);assert p.wait()==0
s=root/rel;h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ms='7bb29418df959c0d1aae4bb29d8c9dd81680eb6d758409f983d0c33077cf860a';assert h(s/'SHA256SUMS')==ms
for l in (s/'SHA256SUMS').read_text().splitlines():
 dig,path=l.split(); assert h(s/path)==dig
assert h(pre/'prerequisites.json')=='b99b2eeff9b445978b2b3d9275a58e0ced195176b444ee6294ec4f0329b6c4ef'
for x in json.loads((pre/'prerequisites.json').read_text()):
 assert h(Path(x['path']))==x['olean_sha256'] and h(old/'mathlib-source'/(x['module'].replace('.','/')+'.lean'))==x['source_sha256']
(root/'prerequisites').symlink_to(old/'prerequisites');(root/'mathlib-source').symlink_to(old/'mathlib-source')
(D/'prerequisites.json').write_bytes((pre/'prerequisites.json').read_bytes());(D/'workdir').write_text(str(root)+'\n')
(D/'source-lock.json').write_text(json.dumps(dict(commit=c,rel=rel,tree=subprocess.check_output(['git','-C',repo,'rev-parse',c+':'+rel],text=True).strip(),manifest_sha256=ms,dependency_receipt_sha256=h(pre/'receipt.json')),indent=2)+'\n')
