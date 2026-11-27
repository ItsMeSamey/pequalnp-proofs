import fcntl,resource,signal,time,json,hashlib,random
from pathlib import Path
from itertools import product
from math import prod
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.03,.03)
import guarded_prism as gp,greedy_cayley as gc,guarded_original_count as whole
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(gp.__file__)=='cd8b05d56e0f97da13d98024a15474b3dfb50793fab09bce7f877dcf065742a8'
assert sha(gc.__file__)=='0eb85f8ecb0d972d12abab4bba2116680075cc2b28e9227375cf9352b8d33147'
assert sha(whole.__file__)=='4599fc2cea6ac93b62b562e7068f1f06dd85945a51386543ad1d3a52989180aa'
rng=random.Random(739)
def build(v,R,wrong=False):
    es=[(2*i+1,2*i+2) for i in range(v//2)]+[(i+1,(i+2)%v+1) for i in range(v)]
    if wrong:
        es=[tuple({1:7,7:1}.get(i,i) for i in e) for e in es]
    real=[[u,w,v+j+1] for j,(u,w) in enumerate(es)]
    g=v+len(es)+1
    fill=[[g,i+1,(i+k)%v+1] for i in range(v) for k in range(1,R+1)]
    return g,real,fill,es
def shuffle(n,rows):
    p=list(range(1,n+1))
    rng.shuffle(p)
    out=[[p[i-1] for i in r] for r in rows]
    rng.shuffle(out)
    for r in out:rng.shuffle(r)
    return out
n,real,_,_=build(8,2)
rows=shuffle(n,real+[[n]])
leaf=gp.supplied_leaf(n,rows)
assert leaf and gp.supplied_leaf(n,rows+[[1]]) is None
physical=gc.prism_profile_oracle(rows)
N=1<<n
full=(1<<N)-1
bits=[]
for i in range(n):
    s=1<<i
    w=((1<<s)-1)<<s
    k=2*s
    while k<N:w|=w<<k;k*=2
    bits.append(w)
viol=[]
for r in rows:
    hit=0
    for l in r:hit|=bits[l-1]
    viol.append(full^hit)
q=len(rows)
def truth(w):
    a=full
    for i,z in enumerate(viol):a &= z if w>>i&1 else full^z
    return a
for w in [0,1,(1<<q)-1,173,92]:
    a=truth(w)
    assert leaf.weight(w)==a.bit_count()==physical(w)
    assert leaf.weight(w,[1,-2])==(a&bits[0]&(full^bits[1])).bit_count()
    assert leaf.weight(w,[-1,1])==0
alive=full
def parity(mask):
    p=0
    for i,z in enumerate(viol):
        if mask>>i&1:p^=z
    return p
def sweep(length):
    global alive
    scores={}
    best=None
    for r in product(tuple(product(range(q),range(2))),repeat=length):
        mask=0
        for i,c in r:mask^=c<<i
        if mask not in scores:scores[mask]=(alive&(full^parity(mask))).bit_count()
        if best is None or scores[mask]<best[2]:best=(list(r),mask,scores[mask])
    alive &= full^parity(best[1])
    return best
# Every prefix row is selected from the empty start by actual scoring, at fixed P=2.
prefix=[sweep(2)[1] for _ in range(q-3)]
expected=[sweep(2) for _ in range(5)]
called=[]
def weight(w):
    called.append(w)
    assert physical(w)==truth(w).bit_count()
    return leaf.weight(w)
assert list(gc.replay(q,prefix,2,5,weight))==expected
assert len(called)==len(set(called))==8
guard()
del bits,viol,full,alive
n,real,fill,es=build(12,2)
split=[0,0]
for a in range(1<<12):
    count=prod(sum(bool((a>>(u-1)&1) or (a>>(w-1)&1) or z) for z in (0,1)) for u,w in es)
    for g in (0,1):
        if all(g or (a>>(u-1)&1) or (a>>(w-1)&1) for _,u,w in fill):split[g]+=count
raw=shuffle(n+2,real+fill)
assert whole.count_original(n+2,raw)==4*sum(split)
assert whole.count_original(n+2,raw,source_radius=True) is None
n,bad,fill,_=build(12,2,True)
assert whole.count_original(n,shuffle(n,bad+fill)) is None
for v in [38,40]:
    n,real,fill,_=build(v,18)
    obj=gp.original(n,shuffle(n,real+fill))
    assert obj and len(obj.leaf.columns)==v//2
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(checker=sha(__file__),prefix=prefix,suffix=expected,word_calls=called,parent_by_guard=split,whole_with_unused=4*sum(split),recognized=[38,40],cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
