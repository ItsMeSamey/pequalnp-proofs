from collections import Counter
from itertools import product
from pathlib import Path
import fcntl,resource,signal,time,hashlib,json,random
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.03,.03)
import aligned_b_scalar as uut
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(uut.__file__)=='7e7b1a75d215541292a1c9dcf91c8600ba5bd0e42c8ac6083b261e9bba0b66b7'
rng=random.Random(832)
v=6
real_edges=[(2*i,2*i+1) for i in range(3)]+[(i,(i+2)%v) for i in range(v)]
filler_edges=[(i,(i+k)%v) for i in range(v) for k in (1,2)]
n=16
perm=list(range(1,n+1));rng.shuffle(perm)
g=perm[-1]
real=[[perm[a],perm[b],perm[v+j]] for j,(a,b) in enumerate(real_edges)]
filler=[[g,perm[a],perm[b]] for a,b in filler_edges]
raw=real+filler
rng.shuffle(raw)
for c in raw:rng.shuffle(c)
obj=uut.from_original(n,raw,g)
assert obj is not None
can=[(-g,)]+[tuple(y for y in c if y!=g) for c in raw if g in c]
assert obj.clauses==tuple(can)
cs=can[:];rng.shuffle(cs)
leaf=uut.recognize(n,cs)
assert leaf and leaf.radius==2 and uut.recognize(n,[(g,),*can[1:]]) is None
assert uut.from_original(n,raw+[[perm[0],perm[3],perm[6]]],g) is None
def rawbit(x,l):return bool(x>>(abs(l)-1)&1)==(l>0)
patterns=Counter()
pins=(perm[0],-perm[8],-g)
pinned=Counter()
parent_false=0
active=sorted(perm[:6]+[g])
# All original 16-bit assignments. Compute B words once per active-bit pattern.
word_cache={}
for x in range(1<<n):
    a=x&sum(1<<(i-1) for i in active)
    if a not in word_cache:
        word_cache[a]=sum(1<<j for j,c in enumerate(cs) if not any(rawbit(a,l) for l in c))
    w=word_cache[a]
    patterns[w]+=1
    if all(rawbit(x,l) for l in pins):pinned[w]+=1
    if not rawbit(x,g) and all(any(rawbit(x,l) for l in c) for c in raw):parent_false+=1
q=len(cs)
assert obj.weight(0)==patterns[0]==parent_false
for w in range(1<<q):assert leaf.weight(w)==patterns[w]
for w in set(patterns)|{95,113,507}:
    assert leaf.weight(w,pins)==pinned[w]
    assert leaf.weight(w,[g,-g])==0
gid=next(i for i,c in enumerate(cs) if len(c)==1)
assert all(patterns[w]==patterns[w^(1<<gid)] for w in patterns)
rows=list(product(tuple(product(range(q),range(2))),repeat=2))
def mask(r):
    a=0
    for j,c in r:a^=c<<j
    return a
masks=list(map(mask,rows))
prefix=[]
current=patterns.copy()
history=[]
checked=0
for stage in range(10):
    values={m:sum(k for w,k in current.items() if (w&m).bit_count()%2==0) for m in set(masks)}
    first=min(range(len(rows)),key=lambda j:values[masks[j]])
    if stage in (6,7,8,9):
        for c,score in values.items():
            assert leaf.score(prefix,c,word_cap=1<<q)==score
            checked+=1
        assert leaf.score(prefix,0,word_cap=0) is None
        direct=sum(k for w,k in pinned.items() if all((w&h).bit_count()%2==0 for h in [*prefix,masks[first]]))
        assert leaf.score(prefix,masks[first],pins,word_cap=1<<q)==direct
    h=masks[first]
    prefix.append(h)
    history.append((h,values[h]))
    current=Counter({w:k for w,k in current.items() if (w&h).bit_count()%2==0})
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(checker=sha(__file__),target=sha(uut.__file__),reachable=len(patterns),all_words=1<<q,zero_count=patterns[0],original_guard_false=parent_false,prefix=history,scalar_intersections=checked,cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
