import json
from random import Random
from itertools import combinations,product
from time import perf_counter_ns
from gate_factors import *
from successor import solve as incumbent, compile_cnf
from original_cnf import accepts_cnf


def hide(n,g,out):
    j=out.bit_length()-n-2
    assert out==1<<(n+j+1) and j==len(g)-1
    a,b=g[j]
    g=g[:j]+[(a,b^2),(a,2)]
    return n,g,(1<<(n+len(g)))^(1<<(n+len(g)-1))


def tseitin(size,odd,complete=False):
    edges=list(combinations(range(size),2)) if complete else [(i,(i+1)%size) for i in range(size)]
    cs=[]
    for v in range(size):
        incident=[j+1 for j,e in enumerate(edges) if v in e]
        charge=(v in ([0] if odd else [0,1]))
        for vals in product((0,1),repeat=len(incident)):
            if sum(vals)%2!=charge:cs.append([(-j if b else j) for j,b in zip(incident,vals)])
    return len(edges),cs


def test():
    r=Random(590)
    count=0
    for _ in range(250):
        n=r.randrange(1,7)
        gs=[(r.getrandbits(n+j+1),r.getrandbits(n+j+1)) for j in range(r.randrange(1,8))]
        last=r.getrandbits(n+len(gs)+1)
        cert=discover(n,gs,last)
        if cert:
            count+=1
            assert verify(n,gs,last,cert)
            a,b=cert['forms']
            for x in range(1<<n):
                assert portfolio.evaluate(n,gs,last,x)==(portfolio.evaluate(n,gs,a,x)&portfolio.evaluate(n,gs,b,x))
    return count

if __name__=='__main__':
    print('certified among 250 random readouts',test())
    results={}
    for name,size,clique in [('cycle',6,False),('K4',4,True)]:
        for odd in (False,True):
            n,cs=tseitin(size,odd,clique)
            g,y=compile_cnf(n,cs)
            for visible,f in [('visible',(n,list(g),y)),('distributed',hide(n,list(g),y))]:
                n,gates,out=f
                for x in range(1<<n):assert portfolio.evaluate(*f,x)==accepts_cnf(cs,x)
                rows={}
                for tag,route in [('prior_complete',incumbent),('prior_pair',proposer.solve),('certified_pair',solve)]:
                    now=perf_counter_ns();result=route(*f)
                    rows[tag]=dict(result,outer_ns=perf_counter_ns()-now)
                    if result['status']!='skip':assert result['status']==('unsat' if odd else 'sat')
                    if result['status']=='sat':assert accepts_cnf(cs,result['witness'])
                results[f'{name}_{odd}_{visible}']=dict(n=n,clauses=len(cs),ands=len(gates),rows=rows)
                print(name,odd,visible,[(k,v['status']) for k,v in rows.items()])
    open('results.json','w').write(json.dumps(results,indent=2)+'\n')
