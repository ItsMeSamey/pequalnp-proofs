from prefix import solve,ROOT,accepts_cnf
from directed import TailOrbits,BlockTranslation
import json
from random import Random

def narrow(m,bad):
    t=m+1;rows=[]
    for i in range(m):
        s=i+1;x=m+2+5*i;y=x+1;u=x+2;v=x+3;z=x+4
        rows.extend([(s,-x),(s,-y),(-s,x),(s,-x,z)])
        for lhs,rhs in ((x,u),(y,v)):
            rows.extend([(t,-lhs,rhs),(t,lhs,-rhs),(-t,-lhs,-rhs),(-t,lhs,rhs)])
    if bad:rows.extend([(t,),(-t,)])
    return 6*m+1,rows

out=[]
for m in (2,3,4):
    for bad in (False,True):
        n,rows=narrow(m,bad)
        for mode,orb in [('ordinary',None),('equality',TailOrbits(n)),('directed',BlockTranslation(n))]:
            ans=solve(n,rows,orbit=orb)
            assert ans['status']==('unsat' if bad else 'sat')
            assert ans['cost']['highwater']==(1 if mode=='directed' else 1<<m),(m,mode,ans)
            out.append(dict(m=m,bad=bad,mode=mode,strict=getattr(orb,'strict',0),tests=getattr(orb,'tests',0),**ans))
print('18 method/fixture comparisons verified')
rng=Random(1945)
for i in range(160):
    n=rng.randrange(2,8)
    rows=[tuple(rng.randrange(1,n+1)*rng.choice((-1,1)) for _ in range(rng.randint(1,3))) for j in range(rng.randrange(2,13))]
    truth=any(accepts_cnf(rows,x) for x in range(1<<n))
    r=solve(n,rows,orbit=BlockTranslation(n))
    if r['status']!='skip':assert truth==(r['status']=='sat')
open('translated.json','w').write(json.dumps(out,indent=2)+'\n')
