import collections,itertools,json,signal,sys,time
from pathlib import Path
from corpus import cases
P=Path(__file__).resolve().parent
def valid(rows,x):
    return all(any(bool(x>>(abs(v)-1)&1)==(v>0) for v in row) for row in rows)
def fail(*_):raise TimeoutError
def main():
    start=time.perf_counter()
    sys.path.insert(0,str(P.parent/'selector-prefix-antichain'))
    import prefix,residual
    sys.path.insert(0,str(P.parent/'selector-proxy-native'))
    from proxy import solve_cnf
    signal.signal(signal.SIGALRM,fail)
    with (P/'results.jsonl').open('x') as out:
        for name,n,rows,expected in cases():
            if n<=13:
                models=[x for x in range(1<<n) if valid(rows,x)]
                if expected is not None and bool(models)!=expected:raise ValueError(name)
                expected=bool(models)
            assert expected is not None
            for kind in ('baseline','wrapper'):
                for cap in (None,1):
                    r=dict(name=name,n=n,m=len(rows),expected=expected,kind=kind,cap=cap)
                    left=100-(time.perf_counter()-start)
                    if left<=0:r['status']='omitted'
                    else:
                        t=time.perf_counter_ns()
                        try:
                            signal.setitimer(signal.ITIMER_REAL,min(3,left))
                            opts={} if cap is None else dict(state_cap=cap)
                            if kind=='baseline':
                                ob=residual.ResidualTranslation(n)
                                ans=prefix.solve(n,rows,orbit=ob,**opts)
                                r.update(tests=ob.tests,strict=ob.strict)
                            else:ans=solve_cnf(n,rows,**opts)
                            status=ans['status'].lower()
                            if status in ('sat','unsat') and (status=='sat')!=expected:raise ValueError((r,ans))
                            if status=='sat':
                                w=ans['witness']
                                if type(w)!=int or not 0<=w<1<<n or not valid(rows,w):raise ValueError((r,w))
                            r.update(status=status,result=ans)
                        except TimeoutError:r['status']='timeout'
                        finally:signal.setitimer(signal.ITIMER_REAL,0)
                        r['ns']=time.perf_counter_ns()-t
                    print(json.dumps(r),file=out,flush=True)
if __name__=='__main__':main()
