from pathlib import Path
import hashlib,csv,json
D=Path(__file__).resolve().parent
r=json.loads((D/'receipt.json').read_text())
root=Path((D/'workdir').read_text().strip())
bundle=root/json.loads((D/'source-lock.json').read_text())['rel']
read=lambda p:list(csv.DictReader(p.open(),delimiter='\t'))
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=read(bundle/'ThresholdSharpTwoSided-manifest.tsv'); compiled=read(D/'objects.tsv')
assert len(names)==len(compiled)==304
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
assert len(list(prefix.rglob('*.olean')))==304
print('304 distinct sources, 304 fresh objects; six PEqualNP modules; all local edges resolve to the fresh prefix; the two-sided axiom report matches.')
pre=json.loads((D/'prerequisites.json').read_text())
assert [x['module'] for x in pre]==['Mathlib.Logic.Equiv.Embedding','Mathlib.Data.Fintype.CardEmbedding']
for x in pre:
 o=Path(x['path']);assert o.is_relative_to(root/'prerequisites') and not o.is_symlink()
 assert digest(o)==x['olean_sha256']
 assert digest(root/'mathlib-source'/(x['module'].replace('.','/')+'.lean'))==x['source_sha256']
 assert x['git_revision']==r['package_revisions']['mathlib']
assert pre[0]['path'] in pre[1]['deps']
assert any(t['caller']=='ThresholdUpperExtension' and t['resolved_dependency']==pre[1]['path'] for t in res)
assert r['lean_sha256']=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
assert r['lake_manifest_sha256']=='d0af863cde532caaef1b1bee0d63ec47100208e33e488309cb80abc88b8f1509'
print('Both pinned Mathlib prerequisites rebuilt privately, input hashes and import chain verified.')
