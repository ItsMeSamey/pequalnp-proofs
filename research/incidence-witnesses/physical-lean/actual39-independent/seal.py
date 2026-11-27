from inventory import *
import re
d=P(__file__).resolve().parent
m=json.loads((d/'frozen.json').read_text());r=json.loads((d/'ledger.json').read_text())
assert len(r)==len(m)==39 and set(r)==set(m)
axioms={}
for n,v in r.items():
 for k in ['source','object','log']:assert v[k]==m[n][k]
 z=(d/(n+'.log')).read_text()
 assert 'sorryAx' not in z and 'error:' not in z
 for a,ll in re.findall(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]",z):
  terms=ll.split(', ');assert set(terms)<={'propext','Classical.choice','Quot.sound'}
  axioms[a]=terms
assert set(axioms['IncidenceWarmActualPointCap.paid'])=={'propext','Classical.choice','Quot.sound'}
(d/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
receipt=dict(archive=m['IncidenceWarmActualPointCap']['archive'],commit=m['IncidenceWarmActualPointCap']['commit'],ledger=sha(d/'ledger.json'),reports=len(axioms),axioms=sha(d/'axioms.json'),new_objects=39,standard_lean='4.36.0',bound='Chosen warm edits among all physically once-read point inputs on C, <=3213.')
(d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(sha(d/'receipt.json'))
