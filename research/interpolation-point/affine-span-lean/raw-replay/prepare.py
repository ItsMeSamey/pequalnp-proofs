from pathlib import Path
import json,subprocess,hashlib,tempfile
D=Path(__file__).resolve().parent;prev=D.parent/'review-plane-sampler';prevR=Path((prev/'workdir').read_text().strip());old=json.loads((prev/'receipt.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(prev/'receipt.json')=='347e92b3b21e7b4df166e76ce818137cb2373caffa54228029cfc98f57a10d36'
c='33c8dd2d8a4c7003feb3cd4018ee17e615c23d29';rel='research/interpolation-point/affine-span-lean';repo='/workspace/pnp-research';R=Path(tempfile.mkdtemp(dir='/dev/shm',prefix='review-plane-raw-'));s=R/rel
p=subprocess.Popen(['git','-C',repo,'archive',c,rel],stdout=subprocess.PIPE);subprocess.run(['tar','-x','-C',R],stdin=p.stdout,check=True);assert p.wait()==0
assert sha(s/'RAW-SOURCES.sha256')=='18ad389c94c018c5c25fe7120fb921bfbf3035d64ccff5d611e7058073231db7'
assert sha(s/'producer/raw-manifest.sha256')=='81735e45aa91bb6167fdce759f067463b2255cad594a8a21b32003b621a3542a'
for line in (s/'RAW-SOURCES.sha256').read_text().splitlines():
 h,f=line.split();assert sha(s/f)==h
for m in old['modules']:assert sha(s/(m['module']+'.lean'))==m['source_sha256']
for filename,h in [('prerequisites.json','9755dfb10c0267b7e51bb7d37ac67b7fa51c7536b22daa02952fe38a5a5d1741'),('reused-prerequisites.json','b99b2eeff9b445978b2b3d9275a58e0ced195176b444ee6294ec4f0329b6c4ef')]:
 assert sha(prev/filename)==h
 for m in json.loads((prev/filename).read_text()):assert sha(Path(m['path']))==m['olean_sha256']
 (D/filename).write_bytes((prev/filename).read_bytes())
(R/'prerequisites').symlink_to(prevR/'prerequisites');(R/'mathlib-source').symlink_to(prevR/'mathlib-source')
(D/'source-lock.json').write_text(json.dumps(dict(commit=c,tree=subprocess.check_output(['git','-C',repo,'rev-parse',c+':'+rel],text=True).strip(),rel=rel,manifest_sha256=sha(s/'RAW-SOURCES.sha256'),producer_manifest_sha256=sha(s/'producer/raw-manifest.sha256'),sampler_receipt_sha256=sha(prev/'receipt.json')),indent=2)+'\n');(D/'workdir').write_text(str(R)+'\n')
