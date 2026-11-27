"""Sequential precommitted complete-mode runs, with per-process wall limit."""
import json, multiprocessing as mp, time
from pathlib import Path
import sys
from corpus import corpus
from oracle import accepted,oracle
solver_dir=Path(__file__).resolve().parent.parent/'complete-cnf-source'

def run_one(pipe,n,clauses):
    sys.path.insert(0,str(solver_dir))
    from combined_cnf import solve_cnf
    try:pipe.send(('result',solve_cnf(n,clauses,complete=True)))
    except Exception as error:pipe.send(('error',repr(error)))
    finally:pipe.close()

def main():
    total=0
    path=Path(__file__).with_name('results.jsonl')
    context=mp.get_context('fork')
    with path.open('w') as out:
        for name,n,clauses,basis in corpus():
            expected=oracle(name,n,clauses,basis)
            item=dict(name=name,n=n,m=len(clauses),literals=sum(map(len,clauses)),expected=expected)
            if n>12 and any(len(c)>2 for c in clauses):
                item['outcome']='omitted-unbounded-fallback'
            elif total>=45:
                item['outcome']='omitted-total-time'
            else:
                src,dst=context.Pipe(False)
                start=time.perf_counter()
                process=context.Process(target=run_one,args=(dst,n,clauses))
                process.start()
                dst.close()
                if src.poll(min(3,45-total)):
                    typ,ret=src.recv()
                    item['outcome']=typ
                    if typ=='result':
                        item['solver']=ret
                        if ret['status']!=('sat' if expected['sat'] else 'unsat'):raise AssertionError(item)
                        if expected['sat']:
                            w=ret['witness']
                            assert type(w)==int and 0<=w<1<<n and accepted(clauses,w)
                    else:item['error']=ret
                else:
                    process.kill();item['outcome']='timeout'
                process.join()
                src.close()
                elapsed=time.perf_counter()-start
                item['process_seconds']=elapsed
                total+=elapsed
            print(json.dumps(item),file=out,flush=True)
    print('total process wall seconds',total)
if __name__=='__main__':main()
