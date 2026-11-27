import json
from collections import Counter
from pathlib import Path
from cut199_donor_port_module import classify
base=Path(__file__).resolve().parent
banks=json.loads((base/'cut199-all-five-left.json').read_text())
result=[]
for i,w in enumerate(banks):
    ok=[s for s in range(1,32) if (s>>3) in (1,2) and classify(w,s)]
    result.append(ok)
print(Counter(tuple(v) for v in result))
(base/'cut199-all-five-modules.json').write_text(json.dumps(result))
