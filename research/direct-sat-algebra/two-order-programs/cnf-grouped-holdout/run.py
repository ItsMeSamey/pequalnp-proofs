from corpus import corpus
import multiprocessing as mp
from pathlib import Path
import time,sys,json
P=Path(__file__).resolve().parent
def accepts(rows,x):
    return all(any(((x>>(abs(i)-1))&1)==(i>0) for i in row) for row in rows)
def worker(pipe,mode,n,rows):
    try:
        sys.path.insert(0,str(P.parent/'complete-cnf-source'))
        from combined_cnf import solve_cnf
        if mode=='enhanced':
            from adapter import grouped
            t=time.perf_counter_ns()
            report=grouped(n,rows)
            pipe.send(('grouped',report,time.perf_counter_ns()-t))
            if report['status'].lower() in ('sat','unsat'):
                pipe.send(('done',report))
                return
        result=solve_cnf(n,rows,complete=True)
        pipe.send(('original',result))
        pipe.send(('done',result))
    except BaseException as e:
        pipe.send(('error',repr(e)))
    finally:pipe.close()
def main():
    ctx=mp.get_context('fork')
    used=0
    with (P/'results.jsonl').open('x') as out:
        for name,n,rows in corpus():
            cnt=sum(accepts(rows,x) for x in range(1<<n))
            for mode in ('baseline','enhanced'):
                rec=dict(name=name,n=n,clauses=len(rows),models=cnt,mode=mode,stages=[])
                if used>=80:rec['status']='omitted'
                else:
                    rx,tx=ctx.Pipe(False)
                    proc=ctx.Process(target=worker,args=(tx,mode,n,rows))
                    start=time.perf_counter()
                    proc.start();tx.close()
                    while rx.poll(max(0,min(3,80-used)-(time.perf_counter()-start))):
                        try: msg=rx.recv()
                        except EOFError:break
                        if msg[0]=='done':
                            result=msg[1];status=result['status'].lower()
                            if status!=('sat' if cnt else 'unsat'):raise ValueError(rec,result)
                            if cnt:
                                x=result['witness']
                                if type(x)!=int or not 0<=x<1<<n or not accepts(rows,x):raise ValueError(rec,result)
                            rec['status']=status;break
                        rec['stages'].append(msg)
                        if msg[0]=='error':rec['status']='error';break
                    if 'status' not in rec:
                        rec['status']='timeout-or-incomplete';proc.kill()
                    proc.join();rx.close()
                    elapsed=time.perf_counter()-start;rec['wall_s']=elapsed;used+=elapsed
                print(json.dumps(rec),file=out,flush=True)
if __name__=='__main__':main()
