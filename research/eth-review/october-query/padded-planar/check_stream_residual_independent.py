from collections import Counter
from itertools import product
from pathlib import Path
import fcntl,hashlib,json,resource,signal,time
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import ordered_score_stream as stream
import late_residual_moments as basic
import late_residual_primitive as primitive
import late_moment_decoder as direct
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
hashes=[sha(mod.__file__) for mod in (stream,basic,primitive)]
assert hashes==['2a1878c78f849a513b36f8ac80ca8cc6aac26cb7ada44a13ec06ffc0f4ed36fc','27b419b09ba0000df01fafd3324b7026b7808773542bf8c5d7661994e1a17dee','229b7ddc8efb59b408d4fe0d13b5d48cf91cdd122eff1ecaa159a3a68f965b53']
def odd(x):return x.bit_count()&1
def truth(n,cnf,prefix):
    words=[]
    for assignment in range(1<<n):
        word=sum(1<<i for i,c in enumerate(cnf) if
                 all(((assignment>>(abs(l)-1))&1)!=(l>0) for l in c))
        if all(not odd(word&h) for h in prefix):words.append(word)
    return words
def mask(row):
    # Evaluate index-wise odd multiplicities, preserving every physical token.
    return sum((sum(c for j,c in row if j==i)%2)<<i for i in set(j for j,c in row))
def verify(m,words,log,order=3):
    L=order
    w=Counter(words)
    n=sum(w.values())
    def score(h):return sum(k for x,k in w.items() if not odd(x&h))
    rows=list(product(tuple((i,c) for i in range(m) for c in range(2)),repeat=L))
    scores=[score(mask(row)) for row in rows]
    expected=tuple(sum(k*x**i for x,k in w.items()) for i in range(order+1))
    called=[]
    def physical(row):
        called.append(row)
        return score(mask(row))
    got=stream.integrate(m,L,n,physical)
    assert called==rows
    assert got==(expected,rows[scores.index(min(scores))],min(scores))
    # Compute scaled Walsh weights separately by the complete truth-table transform.
    for h in range(1<<m):
        assert list(stream.scaled_coefficients(m,order,h))==[
            sum((-1 if odd(x&h) else 1)*x**k for x in range(1<<m)) for k in range(order+1)]
    expected_atoms={x:k for x,k in w.items() if x}
    s=len(expected_atoms)
    assert sha(direct.__file__)=='e1eb617080b442962791c85b514fa7967002634d45e876c6bbc0ba6f0d89cbf4'
    extended=tuple(sum(k*x**j for x,k in w.items()) for j in range(2*s+2))
    for supplied in (None,w[0]):
        assert direct.decode(m,extended,supplied)==(w[0],expected_atoms)
        if order>=2*s+int(supplied is None):
            assert direct.decode(m,got[0],supplied)==(w[0],expected_atoms)
    for dec in (basic,primitive):
        for model in (w[0],None):
            got=dec.recover(m,2*s+1,model,score,max_atoms=s,work_cap=100000)
            assert got==(w[0],expected_atoms),(model,got,w)
            if s>0:
                assert dec.recover(m,2*s+1,model,score,max_atoms=s-1,work_cap=100000) is None
    log.append(dict(hist=dict(w),winner=got is not None,min_score=min(scores),first=rows[scores.index(min(scores))],negative_character=min(2*v-n for v in scores)<0,physical=len(rows)))
log=[]
for cnf,prefix in [([(1,),(1,),(2,3)],[]), ([(1,),(-1,),(1,)],[]),
                   ([(1,),(1,),(2,3)],[1]), ([(1,),(1,),(2,3)],[1,4]), ([(1,),(-1,),(1,)],[3])]:
    verify(len(cnf),truth(3,cnf,prefix),log)
# Large nonuniform integer weights via unused bits; no assignment materialization.
verify(3,{0:2**70+1,1:2**73+17,6:3},log,2)
assert any(r['negative_character'] for r in log)
import ordered_survivor_handoff as handoff
assert sha(handoff.__file__)=='63dcb51c1b22f689d41d4ffe2d26e01ad698256981e996ebbda18f09c70689e8'
rows=list(product(((0,0),(0,1),(1,0),(1,1)),repeat=6))
raw=truth(3,[(1,),(2,)],[])
survivors=raw[:]
expected_winners=[]
for stage in range(3):
    vals=[sum(not odd(word&mask(row)) for word in survivors) for row in rows]
    first=rows[vals.index(min(vals))]
    expected_winners.append((first,min(vals)))
    survivors=[word for word in survivors if not odd(word&mask(first))]
current=raw[:]
seen=0
def observe(stage,row,value):
    global seen,current
    phase,pos=divmod(seen,len(rows))
    assert phase==stage and row==rows[pos]
    if pos==0 and stage:
        last=mask(expected_winners[stage-1][0])
        current=[word for word in current if not odd(word&last)]
    assert value==sum(not odd(word&mask(row)) for word in current)
    seen+=1
def train(row):return sum(not odd(word&mask(row)) for word in raw)
actual=handoff.ordered_handoff(2,6,len(raw),train,rounds=3,max_atoms=3,max_lists=3*len(rows),models=2,observe=observe)
assert actual==(2,tuple(expected_winners),dict(Counter(w for w in survivors if w))) and seen==3*len(rows)
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(hashes=hashes,checker=sha(__file__),fixtures=log,handoff_scored=seen,handoff_minima=[v for _,v in expected_winners],cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
