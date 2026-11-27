import os
os.environ['REVIEW_BATCH']='0'
from scalar_replay import *
assert len(knownO)==len(entries)==255 and len(rows)==69 and len(old)==100
baseline={}
for st in ('review-q401','review-q401-increment','review-q401-plus2','review-q401-batches','review-q401-pinrun'):
 s=base/st; rr=json.loads((s/'ledger.json').read_text()) if st.endswith(('batches','pinrun')) else json.loads((s/'receipt.json').read_text())['modules']
 for n,v in rr.items():baseline[n.removesuffix('.lean').replace('/','.')]=v
datas={};reports={}
for n,r in entries.items():
 v=(rows|old).get(n) or baseline[n];assert v['source']==r['source_sha256'] and v['object']==r['object_sha256']
 datas[n]={'source':v['source'],'object':v['object'],'stage':'new' if n in rows else 'bilateral' if n in mods else 'older'}
 if n in rows:
  zlog=(sd/(n+'.log')).read_text()
  for name,raw in re.findall(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]",zlog):
   ls=raw.split(', ');assert set(ls)<={'propext','Classical.choice','Quot.sound'};reports[name]=ls
for n in ['IncidenceOfficialScalar.physical_posted401','IncidencePhysical401Caller.scalar']:assert set(reports[n])=={'propext','Classical.choice','Quot.sound'}
for filename,val in [('all255',datas),('axioms',reports)]:(sd/(filename+'.json')).write_text(json.dumps(val,indent=2)+'\n')
result=dict(frozen=cfg,compiler=matrix['compiler'],modules=255,sealed_bilateral=176,other_prior=10,fresh=69,dependency_pins=len(matrix['external_first_matches']),earlier_bilateral_receipt=sha(d/'176-receipt.json'),new_object_ledger=sha(lf),all255=sha(sd/'all255.json'),axioms=sha(sd/'axioms.json'),scalar=datas['IncidencePhysicalScalar401'],posted=datas['IncidencePhysicalPosted401'])
(sd/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(sha(sd/'receipt.json'))
