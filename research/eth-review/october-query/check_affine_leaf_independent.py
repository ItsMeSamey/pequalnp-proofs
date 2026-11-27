from itertools import combinations,product
from pathlib import Path
from functools import lru_cache
from collections import Counter
import fcntl,resource,signal,time,hashlib,json
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import original_dense_driver as src, affine_cover_scalar as aff
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(aff.__file__)=='fbc4d156c2dd32529bdb44da5f43e5e1f952fedc90bcb39fe4a6a94314bfe3a6'
hearts=Counter()
def fixture(v,D,signed_controls=False):
    # Original mixed-filler family, with degree two and reduced thresholds.
    es=[(1+i,1+((i+1)%v)) for i in range(v)]
    if D==1: es=es[2:]+es[:2]
    g=v+1;n=v+1+len(es)
    inp=[]
    for i,(a,b) in enumerate(es):
        z=v+2+i
        inp.append((a,b,z))
        inp.extend((g,1+(i*D+j)%v,z) for j in range(D))
    full=(1<<(1<<n))-1
    @lru_cache(None)
    def sat(c):
        return sum(1<<x for x in range(1<<n) if any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c))
    def model(f):
        w=full
        for c in f:w&=sat(tuple(c))
        return w
    def norm(f):
        canon={frozenset(c) for c in f if not any(-x in c for x in c)}
        return tuple(sorted((tuple(sorted(c)) for c in canon if not any(s<c for s in canon)),key=lambda c:(len(c),c)))
    expected=[]
    def visit(f):
        freq=Counter((len(c),z) for c in f for k in range(1,len(c)) for z in combinations(c,k))
        cand=[(w,-len(z),z) for (w,z),count in freq.items() if count>=2**(w-len(z))]
        if not cand:
            expected.append(f);return
        w,neg,z=min(cand)
        hearts[w,-neg]+=1
        hit=[c for c in f if len(c)==w and set(z)<=set(c)]
        rest=[c for c in f if c not in hit]
        left=norm(rest+[z]);right=norm(rest+[set(c)-set(z) for c in hit]+[(-k,) for k in z])
        a,b=model(left),model(right)
        assert not a&b and a|b==model(f)
        visit(left);visit(right)
    visit(norm(inp))
    observed=[tuple(tuple(c) for c in l) for l in src.leaves(inp,2)]
    assert observed==expected
    trials=0
    records=[]
    for leaf in observed:
        truth=model(leaf)
        fail=[full^sat(c) for c in leaf]
        alive=full;prefix=[];q=len(leaf)
        for step in range(3*n):
            # P=1: the candidate alphabet (i,c) includes a zero row for every i.
            if step and alive==truth:
                # Remaining rows all have the same count; zero row is lexicographically first.
                # Check that zero row once at the stable prefix, then record the repeated tail.
                chk=aff.score(n,leaf,prefix,0,cover=range(1,v+2),assignment_cap=1<<(v+1))
                assert chk['prefix']==chk['score']==truth.bit_count()
                records.append((step,3*n-step))
                break
            masks=[(i,b,(1<<i)*b) for i in range(q) for b in (0,1)]
            if not masks: break
            vals={}
            for i,b,r in masks:
                if r in vals:continue
                want=(alive&(full^fail[i])).bit_count() if b else alive.bit_count()
                chk=aff.score(n,leaf,prefix,r,cover=range(1,v+2),assignment_cap=1<<(v+1))
                assert chk['status']=='exact' and chk['prefix']==alive.bit_count() and chk['score']==want
                vals[r]=want;trials+=1
            i,b,r=min(masks,key=lambda t:vals[t[2]])
            prefix.append(r)
            if b:alive &=full^fail[i]
        assert alive==truth
    assert sum(model(leaf).bit_count() for leaf in observed)==model(inp).bit_count()
    return [v,D,n,len(observed),model(inp).bit_count(),trials,sum(k for j,k in records)]
results=[fixture(4,2),fixture(5,1)]
assert set(hearts)=={(2,1),(3,1),(3,2)},hearts
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(checker=sha(__file__),solver=sha(aff.__file__),source=sha(src.__file__),fixtures=results,hearts={str(k):v for k,v in hearts.items()},cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
