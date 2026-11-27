from random import Random
from residual import certificate,ResidualTranslation
from prefix import solve,diagram
from coset import from_forbidden,translate
from check_translation import narrow
import json
rng=Random(477)
checked=found=declined_true=0
for _ in range(320):
    n=rng.randint(1,5);front=list(range(1,n+1))
    def rand_sig():
        rows=[tuple(rng.choice((-1,1))*rng.choice(front) for _ in range(rng.randint(1,2))) for _ in range(rng.randrange(7))]
        d=diagram(n,rows,front,{'binary_probes':0})
        return None if d is None else from_forbidden(front,d)
    A=rand_sig();B=rand_sig()
    if A is None or B is None:continue
    bs=[rng.randrange(1<<n) for i in range(rng.randrange(1,n+1))]
    words={0}
    for b in bs:words|={w^b for w in words}
    def good(w):
        return all(not(translate(t,sum(((w>>(v-1))&1)<<i for i,v in enumerate(s)))&~B[s]) for s,t in A.items())
    valid={w for w in words if good(w)}
    x=certificate(front,A,B,bs)
    if x is not None:assert x in valid;found+=1
    elif valid:declined_true+=1
    checked+=1
out=[]
for m in (3,5,8):
    for bad in (False,True):
        n,rows=narrow(m,bad);o=ResidualTranslation(n)
        result=solve(n,rows,orbit=o)
        assert result['status']==('unsat' if bad else 'sat') and result['cost']['highwater']==1
        out.append(dict(m=m,bad=bad,strict=o.strict,tests=o.tests,**result))
print('raw-shift checks',checked,'certificates',found,'uncertified inclusions',declined_true)
open('residual.json','w').write(json.dumps(out,indent=2)+'\n')
