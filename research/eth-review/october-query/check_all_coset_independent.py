import fcntl, hashlib, json, os, resource, signal, time
from itertools import combinations
from pathlib import Path
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss <= 30*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.01,.01)
signal.alarm(9)
from all_coset_recognizer import recognize
def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
sha=digest('all_coset_recognizer.py')
assert sha=='56d2c1c422db69c64c0617016f9605cc9741a9b01d04d744b33f8126b5058a35'
def words(b):
    v=[0]
    for u in b: v+= [x^u for x in v]
    return v
def flats(n,t):
    level={frozenset(range(1<<n)):tuple(1<<i for i in range(n))}
    for i in range(t+1):
        yield from level.values()
        if i==t: break
        nxt={}
        for b in level.values():
            for h in range(1,1<<len(b)):
                pivot=(h&-h).bit_length()-1
                c=tuple(x^(b[pivot] if h>>j&1 else 0) for j,x in enumerate(b) if j!=pivot)
                nxt.setdefault(frozenset(words(c)),c)
        level=nxt
def valid(n,polys,b,origin_only=False):
    w=words(b)
    if len(set(w))!=len(w) or any(x<0 or x>=1<<n for x in w):return False
    seen=set()
    for off in range(1 if origin_only else 1<<n):
        if off in seen:continue
        cos=[off^x for x in w]
        seen.update(cos)
        for p in polys:
            a=[sum((m&x)==m for m in p)%2 for x in cos]
            for i in range(len(b)):
                for j in range(len(a)):
                    if j>>i&1:a[j]^=a[j^(1<<i)]
            if any(v and j.bit_count()>2 for j,v in enumerate(a)):return False
    return True
cases=[(4,[[15]],1),(4,[[15]],2),(3,[[7]],1),(3,[[7,7,3]],0),(6,[[7],[56]],1),(4,[],0),(4,[[0],[7,7]],0),(5,[[7,11],[13,14]],1)]
assert valid(4,[[15]],(1,2,4),True) and not valid(4,[[15]],(1,2,4))
from random import Random
rng=Random(7374)
for _ in range(40):
    n=rng.choice([3,4,5])
    t=rng.choice([0,1,2])
    polys=[[rng.randrange(1<<n) for j in range(rng.randrange(1,9))] for i in range(rng.randrange(1,4))]
    cases.append((n,polys,t))
success=0
for idx,(n,p,t) in enumerate(cases):
    ref=any(valid(n,p,b) for b in flats(n,t))
    got=recognize(n,p,t)
    assert (got is not None)==ref,(idx,n,p,t,ref,got)
    if got is not None:
        assert n-t<=len(got)<=n and valid(n,p,got),(idx,got)
        success+=1
guard()
print(json.dumps(dict(sha=sha,checker=digest(__file__),cases=len(cases),yes=success,no=len(cases)-success,origin_only_trap=True,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,cpu_s=time.process_time())))
