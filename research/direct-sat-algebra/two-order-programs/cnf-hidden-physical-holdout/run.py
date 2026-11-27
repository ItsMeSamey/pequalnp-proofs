import json,random,multiprocessing as mp,time,sys
from pathlib import Path
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent/'cnf-hidden-holdout'))
from corpus import cases

def valid(rows,x):
    return all(any(bool((x>>(abs(v)-1))&1)==(v>0) for v in r) for r in rows)

def child(pipe,i,n,rows):
    try:
        sys.path[:0]=[str(P.parent/'selector-variable-compiler'),str(P.parent/'selector-component-native')]
        from compiler import compile_cnf,decode
        from projection import solve
        t=time.perf_counter_ns()
        m,physical,triples=compile_cnf(n,rows)
        ct=time.perf_counter_ns()-t
        t=time.perf_counter_ns()
        g=random.Random(19320917+i)
        perm=list(range(1,m+1));g.shuffle(perm)
        raw=[]
        for row in physical:
            r=[perm[abs(v)-1]*(1 if v>0 else -1) for v in row]
            g.shuffle(r);raw.append(r)
        g.shuffle(raw)
        pipe.send(('compiled',dict(n=m,rows=len(raw),literals=sum(map(len,raw)),compile_ns=ct,relabel_ns=time.perf_counter_ns()-t)))
        ans=solve(m,raw)
        if ans['status']=='sat':
            w=ans['witness']
            if type(w)!=int or w<0 or w.bit_length()>m or not valid(raw,w):raise ValueError('physical replay')
            before=sum(((w>>(j-1))&1)<<i for i,j in enumerate(perm))
            x=decode(before,triples)
            if not valid(physical,before) or not valid(rows,x):raise ValueError('decode')
            ans['decoded']=x
        pipe.send(('result',ans))
    except BaseException as e:pipe.send(('error',repr(e)))
    finally:pipe.close()

def main():
    ctx=mp.get_context('fork')
    total=0
    with (P/'results.jsonl').open('x') as out:
        for i,(name,n,rows) in enumerate(cases()):
            t=time.perf_counter_ns();models=[x for x in range(1<<n) if valid(rows,x)]
            units=[(j+1)*(1 if models[0]>>j&1 else -1) for j in range(n) if models and all((x>>j&1)==(models[0]>>j&1) for x in models)]
            rec=dict(name=name,n=n,source_rows=len(rows),models=len(models),units=units,oracle_ns=time.perf_counter_ns()-t)
            if total>=82:rec['status']='omitted'
            else:
                rx,tx=ctx.Pipe(False);proc=ctx.Process(target=child,args=(tx,i,n,rows))
                t=time.perf_counter();proc.start();tx.close()
                while rx.poll(max(0,min(3,82-total)-(time.perf_counter()-t))):
                    try:k,v=rx.recv()
                    except EOFError:break
                    rec[k]=v
                    if k!='compiled':
                        rec['status']=v['status'] if k=='result' else 'error'
                        break
                if 'status' not in rec:proc.kill();rec['status']='timeout'
                proc.join();rx.close()
                rec['wall_s']=time.perf_counter()-t;total+=rec['wall_s']
                if rec['status'] in ('sat','unsat'):
                    if (rec['status']=='sat')!=bool(models):raise ValueError(rec)
                    if models and rec['result']['decoded'] not in models:raise ValueError(rec)
            print(json.dumps(rec),file=out,flush=True)
if __name__=='__main__':main()
