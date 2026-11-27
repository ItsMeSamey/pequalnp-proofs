from itertools import combinations,product
from pathlib import Path
import fcntl,resource,signal,time,hashlib,json,random
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import guarded_joint_scalar as sol
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(sol.__file__)=='0e3f83ff4d5c436b049c40bc3fdcb80a05fac31229c774e6a0cce942e1e54390'
rng=random.Random(92)
n=11
perm=list(range(1,n+1));rng.shuffle(perm)
cs=[[perm[a],perm[b],perm[4+i]] for i,(a,b) in enumerate(combinations(range(4),2))]+[[perm[-1]]]
rng.shuffle(cs)
for r in cs:rng.shuffle(r)
q=len(cs)
g=next(j for j,r in enumerate(cs) if len(r)==1)
hist={}
for x in range(1<<n):
    w=sum(1<<j for j,r in enumerate(cs) if all(not(x>>(v-1)&1) for v in r))
    hist[w]=hist.get(w,0)+1
assert len(hist)==1<<q
P=2
physical=list(product(tuple(product(range(q),range(2))),repeat=P))
def mask(row):
    u=0
    for j,c in row:u^=c<<j
    return u
masks=[mask(r) for r in physical]
uniq=sorted(set(masks))
rows=[]
closed={0}
history=[]
missing=0
negative_norm=0
guardzero=0
control_count=0
prev=None
for stage in range(9):
    live={w:t for w,t in hist.items() if all(not((w&r).bit_count()%2) for r in rows)}
    N=sum(live.values())
    scores={}
    for c in uniq:
        val=sum(t for w,t in live.items() if (w&c).bit_count()%2==0)
        signed=2*val-N
        ctl=sol.scalar(n,cs,rows,c,budget=10**7)
        assert (ctl['status'],ctl['score'],ctl['signed'],ctl['prefix'])==('exact',val,signed,N)
        scores[c]=val
        control_count+=1
        if stage==0 and c==1<<g:
            assert signed==0
            guardzero+=1
        if prev is not None:
            old_span,h=prev
            if min((c^h^z).bit_count() for z in old_span)>P:missing+=1
        if len(closed)==1<<q:negative_norm+=1
    vals=[scores[c] for c in masks]
    h=masks[vals.index(min(vals))]
    history.append((h,min(vals)))
    prev=(closed.copy(),h)
    closed.update([z^h for z in closed])
    rows.append(h)
assert missing>0 and negative_norm>0 and guardzero
assert sum(hist.values())==1<<n
assert sol.scalar(n,cs,[],1,budget=0)['status']=='budget'
seen=[]
def fb():
    seen.append(1)
    return (1<<n,0)
res=sol.scalar(n,cs,[],1<<g,budget=0,fallback=fb)
assert res['status']=='fallback' and res['score']==1<<(n-1) and seen==[1]
assert sol.scalar(n,cs+[[perm[0]]],[],0,budget=100)['status']=='unsupported'
base=sol.scalar(n+2,cs,rows,0,budget=10**7)
assert base['score']==4*hist[0]
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(checker=sha(__file__),solver=sha(sol.__file__),comparisons=control_count,selected_history=history,guardzero=guardzero,negative_exponent=negative_norm,outside_old_radius=missing,cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
