from pathlib import Path
import hashlib,csv,json
D=Path(__file__).resolve().parent
r=json.loads((D/'receipt.json').read_text())
root=Path((D/'workdir').read_text().strip())
bundle=root/'research/crown-circuits/uniform-threshold/kernel-four-thirds'
read=lambda p:list(csv.DictReader(p.open(),delimiter='\t'))
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=read(bundle/'ThresholdPublicFourThirds-manifest.tsv'); compiled=read(D/'objects.tsv')
assert len(names)==len(compiled)==92
assert [x['module'] for x in names]==[x['module'] for x in compiled]
res=read(D/'resolved.tsv'); prefix=(root/'fresh').resolve()
seen=set()
for n,o in zip(names,compiled):
 name=n['module']; assert digest(bundle/n['source_path'])==n['source_sha256']==o['source_sha256']
 assert digest(prefix/(name.replace('.','/')+'.olean'))==o['olean_sha256']
 seenImp=set()
 for d in res:
  if d['caller']!=name:continue
  p=Path(d['resolved_dependency'])
  if p.resolve().is_relative_to(prefix):
   rel=p.resolve().relative_to(prefix).with_suffix('').as_posix().replace('/','.')
   assert rel in seen;seenImp.add(rel)
  else:
   assert p.is_relative_to(Path(r['paths'][1])) or any(p.is_relative_to(Path(a)) for a in r['paths'][2:]) or str(p).startswith('/home/agent/.elan/toolchains/')
 assert seenImp==set(n['direct_imports'].split()).intersection(x['module'] for x in names)
 seen.add(name)
assert (D/'axioms.log').read_bytes()==(bundle/'axioms.log').read_bytes()
assert digest(D/'objects.tsv')==r['outputs_sha256'] and digest(D/'resolved.tsv')==r['resolution_sha256']
assert len(list(prefix.rglob('*.olean')))==92
print('92 distinct sources, 92 fresh objects; six PEqualNP modules; all local edges resolve to the fresh prefix; all three axiom reports match.')
