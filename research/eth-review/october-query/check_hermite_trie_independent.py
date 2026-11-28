"""04-only differential. Scalar guards come from the direct rational Hermite product."""
import fcntl
import hashlib
import itertools
import json
import os
import resource
import signal
from fractions import Fraction
from pathlib import Path

lock_path = "/workspace/scratch/pnp-native-search.lock"
lock = open(lock_path, "a")
def inode(s):
    return (s.st_dev, s.st_ino)
assert inode(os.stat(lock_path)) == inode(os.fstat(lock.fileno()))
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
assert inode(os.stat(lock_path)) == inode(os.fstat(lock.fileno()))
resource.setrlimit(resource.RLIMIT_CPU, (4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 64*1024
signal.signal(signal.SIGPROF, guard)
signal.setitimer(signal.ITIMER_PROF, .025, .025)
import shell_jet_optimizer as shell
import individual_center_trie_optimizer as trie
def sha(file):
    return hashlib.sha256(Path(file).read_bytes()).hexdigest()
assert sha(shell.__file__)=="b981e5efd56be4c827ddac09b44832897cbd76becd7ca7d8ba12a7a29c726e4c"
assert sha(trie.__file__)=="c7f7bb744f7db6faa77eb97b9d9a07a634a7e1e490d783deee685b8a7cb1c50d"

def val(x):
    return (abs(x)&-abs(x)).bit_length()-1

def requirements(a,p,q):
    result = {}
    for t,n in q.items():
        if not n:
            continue
        h = Fraction(1)
        for s,m in q.items():
            if s!=t and m:
                h *= Fraction(-s,t-s)**m
        h *= Fraction(-t,2<<a)**(n-1)
        result[t] = max(0,p-val(h.numerator)+val(h.denominator))
    return result

def schedules(a,p,caps,uniform):
    groups=[[t for t in caps if caps[t] is not None and val(t)==i] for i in range(a+1)]
    def recurse(i,q):
        if i<0:
            yield q
            return
        group=groups[i]
        if not group:
            yield from recurse(i-1,q)
            return
        tail=sum((val(s)-i)*m for s,m in q.items())
        # Ignore nonnegative same-shell losses only to bound brute enumeration.
        limits=[max(0,1+(caps[t]-p+tail)//(a+1-i)) for t in group]
        words=((k,)*len(group) for k in range(min(limits)+1)) if uniform else itertools.product(*(range(k+1) for k in limits))
        for word in words:
            qq=dict(q)
            qq.update(zip(group,word))
            req=requirements(a,p,qq)
            if all(b<=caps[t] for t,b in req.items()):
                yield from recurse(i-1,qq)
    return recurse(a,{})

def price(t,q,b):
    return (2 if t<0 else 1)*q + abs(b-2) + (q+b)%2

cases=[
 (3,2,{1:3,3:3,5:3},1),
 (2,2,{-4:2,-2:1,2:2,1:0},2),
 (2,1,{-3:2,-1:None,1:2,3:1,2:2},2),
 (2,3,{-4:3,2:0,-2:None,1:0},2),
 (1,1,{-2:0,-1:0,1:0},0),
 (3,1,{},2),
 (2,1,{-4:2,2:2},2),
 (2,1,{-2:3,2:3,1:0},2),
]
active_zero=False
overpurchase=False
individual=[]
for a,p,caps,d in cases:
    valid=[]
    for q in schedules(a,p,caps,False):
        if sum(q.values())<=d:
            continue
        req=requirements(a,p,q)
        expense=sum(min(price(t,q[t],k) for k in range(b,caps[t]+1)) for t,b in req.items())
        valid.append(expense)
    answer=trie.optimize(a,p,caps,d,price)
    assert (answer is None)==(not valid)
    if answer:
        qq={t:m for t,m,_,_ in answer.centers}
        rr=requirements(a,p,qq)
        assert rr=={t:b for t,_,b,_ in answer.centers}
        assert answer.cost==min(valid)==sum(price(t,m,k) for t,m,b,k in answer.centers)
        assert answer.slots==sum(qq.values())>d
        overpurchase |= any(k>b for t,m,b,k in answer.centers)
        active_zero |= any(b==0 for t,m,b,k in answer.centers)
    individual.append(None if answer is None else answer.cost)

uniform_count=0
for a,outer,p,caps in [(1,False,1,(2,2)),(2,False,1,(2,1,None)),
    (2,False,2,(0,1,2)),(2,True,2,(3,)),(3,True,1,(2,2)),
    (3,True,2,(None,0)),(1,True,1,())]:
    L=1<<a
    ts=[t for t in range(-L,L) if t and val(t)<len(caps) and
        (not outer or t<-(L//2) or t>=L//2)]
    allowed={t:caps[val(t)] for t in ts}
    options=list(schedules(a,p,allowed,True))
    sc=lambda i,q,b:q*q+(i+1)*(b+1)
    for d in (0,2,8):
        valid=[q for q in options if sum(q.values())>d]
        g=shell.greatest(a,p,caps,d,outer=outer)
        best=shell.minimum_cost(a,p,caps,d,sc,outer=outer)
        assert (not valid)==(g is None)==(best is None)
        if valid:
            def charges(q):
                return sum(sc(val(t),q[t],b) for t,b in requirements(a,p,q).items())
            assert best.cost==min(charges(q) for q in valid)
            assert all(g.multiplicities[val(t)]>=q[t] for q in valid for t in q)
            for sol in (g,best):
                qq={t:sol.multiplicities[val(t)] for t in ts}
                assert all(sol.precisions[val(t)]==b for t,b in requirements(a,p,qq).items())
        uniform_count+=1
# A high node can erase every digit requirement at a different, lower node.
free=trie.optimize(2,1,{-4:2,1:0},2,lambda t,q,b: b)
assert free and any(b==0 for _,_,b,_ in free.centers)
active_zero=True
extra=trie.optimize(1,1,{1:3},0,lambda t,q,b: abs(2-b))
assert extra and any(k>b for t,m,b,k in extra.centers)
overpurchase=True
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(harness=sha(__file__),individual_costs=individual,uniform_cases=uniform_count,
    active_zero=active_zero,overpurchase=overpurchase,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
