import hashlib,json,zipfile,ast,re
from pathlib import Path
p=Path('/workspace/scratch/protected23-numeric/native-all-four-or21-kernel.zip');sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(p.read_bytes())=='68261abca52fcbbb2d4c934d2de53f01e940ce9fa10eeb05fa7268ffe04dee37'
z=zipfile.ZipFile(p);f=set(z.namelist());assert len(f)==len(z.namelist())
d={k:v for v,k in (line.split('  ',1) for line in z.read('SHA256SUMS').decode().splitlines())}
assert set(d)==f-{'SHA256SUMS'}
for k,v in d.items():assert sha(z.read(k))==v
records=json.loads(z.read('closure.json'));mods={r['module']:r for r in records}
base=Path('/workspace/scratch/official9822-lean/receipts')
orig=dict(d); raw={k:z.read(k) for k in d}
for name,expected in json.loads(z.read('predecessors.json')).items():
 file=p.parent/name;assert sha(file.read_bytes())==expected
 other=zipfile.ZipFile(file)
 for k in other.namelist():
  b=other.read(k);raw.setdefault(k,b);d.setdefault(k,sha(b))
for n,r in mods.items():
 src='source/'+n+'.lean';obj='object/'+n+'.olean';rec=r['receipt']
 assert r['source']==d[src] and r['object']==d[obj]
 x=json.loads(raw.get('receipts/'+rec+'/'+n+'.inputs.json') or raw['receipts/'+n+'.inputs.json'])
 assert x==dict(source=r['source'],imports=r['imports'])
 lines=(base/rec/'digests.txt').read_text().splitlines()
 assert all(any(t.startswith(d[k]+'  ') and t.endswith('/'+Path(k).name) for t in lines) for k in (src,obj))
 for fn,v in r['imports'].items():
  assert sha(Path(fn).read_bytes())==v
  if Path(fn).stem in mods:assert mods[Path(fn).stem]['object']==v
s=z.read('source/ProtectedNumericOriginal.lean').decode()
seed=Path('/workspace/scratch/native-deletion-kernel/NativeDeletionSeeds.lean').read_text()
cols=ast.literal_eval('['+seed.split('def columnWords')[1].split(':= [')[1].split(']')[0]+']')
for kind in ['Pos','Neg']:
 a=ast.literal_eval(re.search(r'def root'+kind+r' .* := (\[.*\])',s)[1]);assert all(mask==sum(((c>>r)&1)<<j for j,c in enumerate(cols)) for mask,r in a);print(kind,len(a))
print('modules',len(mods),'entries',len(d),'target',mods['IncrementOriginal21']['source'],mods['IncrementOriginal21']['object'])
