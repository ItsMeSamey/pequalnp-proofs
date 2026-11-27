from multiprocessing import get_context
from time import perf_counter_ns
from pathlib import Path
import json,sys
from random import Random
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check import coupled
from solver import solve,accepts_cnf
ROOT=Path(__file__).resolve().parent.parent
def worker(pipe,n,rows):
    try:
        sys.path.insert(0,str(ROOT/'complete-cnf-source'))
        from combined_cnf import solve_cnf
        r=solve_cnf(n,rows,complete=False,fallback_limit=128)
        pipe.send((r['status'],r['route'],r.get('witness'),r['cost']['total_elapsed_ns'],r['cost']['fallback_assignments']))
    except BaseException as e:pipe.send(('error',str(e),None,None,None))
    finally:pipe.close()

if __name__=='__main__':
    ctx=get_context('spawn');results=[]
    for m in (4,12):
        for bad in (False,True,"odd_exterior"):
            n,cs=coupled(m,bad is True)
            if bad=="odd_exterior":
                for a,b in ((2,4),(4,6),(6,2)):cs.extend([(a,b),(-a,-b)])
            p=list(range(1,n+1));rng=Random(591+m);rng.shuffle(p);rng.shuffle(cs)
            # Signed cross-pair and unit exteriors are already included in coupled().
            cs=[tuple(p[abs(l)-1]*(1 if l>0 else -1) for l in c) for c in cs]
            new=solve(n,cs,b=1,extract_arities=(3,),orient=True)
            rx,tx=ctx.Pipe(False);q=ctx.Process(target=worker,args=(tx,n,cs));q.start();tx.close()
            if rx.poll(2):
                result=rx.recv()
            else:
                result=('timeout',None,None,None,None)
                q.terminate()
            q.join();rx.close()
            if result[0]=='sat':assert accepts_cnf(cs,result[2])
            if result[0] in ('sat','unsat'):assert result[0]==new['status']
            print(m,bad,new['status'],result[:2],flush=True)
            results.append(dict(m=m,bad=bad,new=new,prior=result,prior_timeout_seconds=2))
    open('comparison.json','w').write(json.dumps(results,indent=2)+'\n')
