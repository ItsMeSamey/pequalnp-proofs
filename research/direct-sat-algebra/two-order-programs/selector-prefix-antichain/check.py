from random import Random
from prefix import solve,accepts_cnf
import json

def family(m,unsat=False):
    t=m+1; rows=[]
    for i in range(m):
        s=i+1;x=m+2+4*i;y=x+1;z=x+2;u=x+3
        rows.extend([(s,x),(-s,x,y),(t,-x,z),(-t,-y,u)])
    if unsat:
        x=m+2;y=x+1
        for v in (x,y):rows.extend([(t,-v),(-t,-v)])
    return 5*m+1,rows

def orbit_family(m,unsat=False):
    t=m+1;rows=[]
    for i in range(m):
        s=i+1;x=m+2+3*i;y=x+1;u=x+2
        rows.extend([(s,-x),(-s,x),(s,-x,y),(t,-x,u),(t,x,-u),(-t,-x,-u),(-t,x,u)])
    if unsat:rows.extend([(t,),(-t,)])
    return 4*m+1,rows

if __name__=='__main__':
    out=[]
    for m in [2,3,4,5]:
        for bad in [False,True]:
            n,rows=family(m,bad)
            for domination in [False,True]:
                r=solve(n,rows,dominance=domination)
                assert r['status']==('unsat' if bad else 'sat')
                assert r['cost']['highwater']==(1 if domination else 1<<m)
                out.append(dict(m=m,bad=bad,dominance=domination,**r))
    rng=Random(7443)
    for it in range(180):
        n=rng.randrange(1,8)
        rows=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randint(0,3))) for j in range(rng.randrange(12))]
        good=any(accepts_cnf(rows,w) for w in range(1<<n))
        for dom in (False,True):
            r=solve(n,rows,dominance=dom)
            if r['status']!='skip':assert (r['status']=='sat')==good
    print('16 constructed comparisons plus 360 exhaustive controls')
    open('receipt.json','w').write(json.dumps(out,indent=2)+'\n')
