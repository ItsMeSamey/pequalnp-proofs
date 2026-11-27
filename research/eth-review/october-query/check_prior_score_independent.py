import fcntl,resource,signal,time,json,hashlib
from pathlib import Path
from itertools import product
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import prior_score_batch as sol
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(sol.__file__)=='74728fa29bcb6583d2e56ffd95c7cb9fdec36aabc10b1129bafd38ffc8f02ef0'
def mask(row):
    v=0
    for j,c in row:v^=c<<j
    return v
receipts=[]
def verify(cs,n,P,stages=3):
    q=len(cs)
    accepted=[]
    for x in range(1<<n):
        v=sum(1<<j for j,r in enumerate(cs) if all(bool(x>>(abs(l)-1)&1)!=(l>0) for l in r))
        accepted.append((x,v))
    phys=list(product(tuple(product(range(q),range(2))),repeat=P))
    masks=[mask(r) for r in phys]
    def trials(words):
        return [sum((v&h).bit_count()%2==0 for x,v in words) for h in masks]
    for stage in range(stages):
        prev=trials(accepted)
        prior=dict(zip(masks,prev))
        h=masks[prev.index(min(prev))]
        retained=[(x,v) for x,v in accepted if (v&h).bit_count()%2==0]
        truth=trials(retained)
        latest=dict(zip(masks,truth))
        first=phys[truth.index(min(truth))]
        for mode in ['mixed','pins','miss','no_work','unavailable','row_cap']:
            calls=[[],[],[]]
            def old(c):
                calls[0].append(c)
                return None if mode=='miss' and c==h else prior[c]
            def fresh(c):
                calls[1].append(c)
                return latest[c]
            def pinned(lits):
                calls[2].append(lits)
                return sum(all(bool(x>>(abs(l)-1)&1)==(l>0) for l in lits) for x,v in accepted)
            res=sol.replay(cs,P,h,old,work_cap=0 if mode in ['no_work','unavailable'] else 10**5,
                           next_score=None if mode=='unavailable' else fresh,
                           pin_count=pinned if mode=='pins' else None,
                           bicliques=((1,2),) if mode=='pins' else (),
                           row_cap=1 if mode=='row_cap' else None)
            met=res['metrics']
            assert [met[k] for k in ('old','fallback','pins')]==list(map(len,calls))
            if mode=='unavailable':assert res['status']=='unresolved'
            elif mode=='row_cap':assert res['status']=='cap'
            else:
                assert res['status']=='exact' and res['scores']==latest
                row=((0,0),)*res['padding']+tuple((j,1) for j in res['support'])
                assert row==first and res['best']==mask(first) and res['score']==min(truth)
                if mode=='no_work':assert calls[0]==[] and len(calls[1])==len(latest)
            receipts.append([q,P,stage,h,mode,met['old'],met['fallback'],met['pins'],met['biclique'],met['edges']])
        accepted=retained
verify([[1],[-1],[2]],3,1)
verify([[1,2],[-1,3],[1,-3],[-1,-2],[4],[4]],5,2)
assert any(r[7] and r[8] for r in receipts)
assert any(r[6] and r[9] for r in receipts)
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(checker=sha(__file__),solver=sha(sol.__file__),instances=len(receipts),mixed=[r for r in receipts if r[4]=='mixed'],cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
