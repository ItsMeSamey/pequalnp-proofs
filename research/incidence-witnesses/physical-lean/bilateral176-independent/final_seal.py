from line_inventory import *
from initial_line_inventory import mods as line3382
ledger=json.loads((d/'ledger.json').read_text())|json.loads((d/'line-ledger.json').read_text())
old={}
for st in ['review-q401','review-q401-increment','review-q401-plus2','review-q401-batches','review-q401-pinrun']:
 root=base/st;rows=json.loads((root/'ledger.json').read_text()) if st.endswith(('batches','pinrun')) else json.loads((root/'receipt.json').read_text())['modules']
 for n,r in rows.items():old[n.removesuffix('.lean').replace('/','.')]=r
bundle={};w=P((d/'workdir').read_text()); ax={}
for n,v in mods.items():
 k=n.replace('.','/');inherits=groups[n]=='prior';r=old[n] if inherits else ledger[n];o=P(known[k]) if inherits else w/'fresh'/(k+'.olean')
 assert r['source']==v['src'] and sha(o)==r['object']==v['object']
 log=z.read(v['log_path']);assert hashlib.sha256(log).hexdigest()==v['log']
 if not inherits:
  assert (d/(n+'.log')).read_bytes()==log
  assert 'sorryAx' not in log.decode()
  for name,vals in re.findall(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]", log.decode()):
   bits=vals.split(', ');assert set(bits)<={'propext','Classical.choice','Quot.sound'};ax[name]=bits
 bundle[n]=dict(source=v['src'],object=v['object'],origin=groups[n],log=v['log'])
for n,v in line3382.items():
 if n in mods:assert mods[n]['src']==v['src'] and mods[n]['object']==v['object']
 else:assert old[n]['source']==v['src'] and old[n]['object']==v['object']==sha(P(known[n]))
assert len(ledger)==100 and len(bundle)==176 and 'IncidenceActualBilateralCensus.retained' in ax
for name,value in [('all176',bundle),('all-axioms',ax)]:(d/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
r=dict(modules=176,previous=76,fresh=100,point=39,additional=61,verified_hashes=sha(d/'all176.json'),axiom_reports=len(ax),axioms=sha(d/'all-axioms.json'),ledger=sha(d/'ledger.json'),additional_ledger=sha(d/'line-ledger.json'),archive_ref=ref,archive_sha=hashlib.sha256(data).hexdigest())
(d/'176-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(sha(d/'176-receipt.json'))
