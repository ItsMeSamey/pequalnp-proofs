from check import run
from itertools import product
import json
cases=[
 ('affine',[tuple((-v if b else v) for v,b in zip((1,2,3),z)) for z in product((0,1),repeat=3) if sum(z)%2]),
 ('meet',[(-1,-2,3),(-2,-3,4)]),
 ('majority',[(1,2),(-2,-3),(3,4)])]
out=[]
for label,rows in cases:
    rows=[tuple(row) for row in rows]
    r=run(4,rows,label,514)
    assert r['status']=='sat' and r['cost']['join']==label.upper()
    out.append(r)
open('class-receipt.json','w').write(json.dumps(out,indent=2)+'\n')
