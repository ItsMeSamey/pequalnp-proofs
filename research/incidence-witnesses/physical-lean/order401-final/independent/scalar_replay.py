"""Read a separately published immutable full-closure archive and reuse exact prior objects."""
from line_inventory import *
import os,time
sd=d/'scalar';sd.mkdir(exist_ok=True)
cfg=json.loads((sd/'frozen.json').read_text())
b=subprocess.check_output(['git','-C','/workspace/pnp-research','show',cfg['ref']]);assert hashlib.sha256(b).hexdigest()==cfg['sha']
arc=zipfile.ZipFile(io.BytesIO(b));mf=next(k for k in arc.namelist() if k.endswith('manifest.json') and not k.endswith('lake-manifest.json'));pre=mf[:-len('manifest.json')];matrix=json.loads(arc.read(mf));entries=matrix['modules']
w=P((d/'workdir').read_text());f=w/'fresh';pr=w/'prior';root=w/'scalar-src';root.mkdir(exist_ok=True)
lf=sd/'ledger.json';rows=json.loads(lf.read_text()) if lf.exists() else {};old=json.loads((d/'ledger.json').read_text())|json.loads((d/'line-ledger.json').read_text())
knownO={};candidates={}
for n,r in entries.items():
 k=n.replace('.','/');raw=arc.read(pre+r['source']);assert hashlib.sha256(raw).hexdigest()==r['source_sha256']
 if n in mods:assert mods[n]['src']==r['source_sha256'] and mods[n]['object']==r['object_sha256']
 if k in known and sha(P(known[k]))==r['object_sha256']:o=P(known[k])
 elif n in rows or n in old:o=f/(k+'.olean');assert sha(o)==r['object_sha256']
 else:candidates[n]=r;continue
 knownO[n]=o
for n,r in matrix['external_first_matches'].items():assert sha(P(r['first_object']))==r['sha256']
lean=P('/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean')
env=os.environ|{'LEAN_PATH':':'.join(map(str,[f,pr,P('/dev/shm/gcycle-t2/mathlib'),*sorted(P('/workspace/pequalnp-proofs/lean/.lake/packages').glob('*/.lake/build/lib/lean'))]))}
from resource_guard import compile_guarded
def run(args,cwd):return compile_guarded(lean,args,cwd,env)
for _ in range(int(os.environ.get('REVIEW_BATCH','3'))):
 n=next((n for n,r in candidates.items() if n not in knownO and all(x not in entries or x in knownO for x in r['imports'])),None)
 if n is None:break
 r=entries[n];k=n.replace('.','/');filename=k+'.lean';s=root/filename;s.parent.mkdir(exist_ok=True,parents=True);s.write_bytes(arc.read(pre+r['source']))
 logkey=pre+'receipts/'+n+'.log';gold=arc.read(logkey).decode() if logkey in arc.namelist() else ''
 canonical=P(r['origin_source']);absolute=str(canonical) in gold or ('/objects/' in r['first_object'] and 'incidence-q401/' not in r['origin_source'])
 if absolute:
  assert sha(canonical)==sha(s);s=canonical
 deps=run(['--deps',s],s.parent).splitlines()
 for x in r['imports']:
  path=knownO[x] if x in entries else P(matrix['external_first_matches'][x]['first_object'])
  assert any(P(q).resolve()==path.resolve() or (x not in entries and sha(P(q))==sha(path)) for q in deps),(n,x)
 o=f/(k+'.olean');o.parent.mkdir(exist_ok=True,parents=True);cwd=s.parent if absolute else root
 log=run(['--root='+str(cwd),'-o',o,s if absolute else filename],cwd)
 assert 'sorryAx' not in log and sha(o)==r['object_sha256'],(n,sha(o),r['object_sha256'])
 if gold:assert gold==log,(n,log,gold)
 (sd/(n+'.log')).write_text(log)
 rows[n]=dict(source=sha(s),object=sha(o),log=sha(sd/(n+'.log')),deps={q:sha(P(q)) for q in deps})
 knownO[n]=o;lf.write_text(json.dumps(rows,indent=2)+'\n'); print(len(rows),n,flush=True)
