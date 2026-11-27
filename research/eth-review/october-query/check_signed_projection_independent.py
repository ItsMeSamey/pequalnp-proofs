"""Check projected relations and witnesses against exhaustive raw truth tables."""
import fcntl, hashlib, json, resource, signal
from pathlib import Path
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 65536
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import signed_cover_projection as impl
def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert digest(impl.__file__)=='37cc4e33a052b0bfa17917e077249e40fcd344df148876164e0105915d72aeee'
stats=dict(relations=0,words=0,sat=0,unsat=0,changed_counts=0)
def accepts(rows,x):
    return all(any(((x>>(abs(v)-1))&1)==int(v>0) for v in row) for row in rows)
def check(n,rows,cover):
    p=impl.project(n,iter(rows),cover=cover)
    models=[x for x in range(1<<n) if accepts(rows,x)]
    groups={}
    for x in models:
        y=sum(((x>>(v-1))&1)<<j for j,v in enumerate(p.core))
        groups.setdefault(y,set()).add(x)
    for y in range(1<<len(p.core)):
        w=p.lift(y)
        assert accepts(p.clauses,y)==(y in groups)
        if y in groups:
            assert w in groups[y]
        else:
            assert w is None
        stats['words']+=1
    stats['relations']+=1
    stats['sat' if models else 'unsat']+=1
    stats['changed_counts']+=len(groups)!=len(models)
    return len(groups),len(models)
template=((1,),(-1,),(2,),(-2,),(1,2),(1,-2),(-1,2),(-1,-2))
for mask in range(256):
    rows=[row for j,row in enumerate(template) if mask>>j&1]
    for cover in (None,[1],[2],[2,1]):
        check(2,rows,cover)
assert check(5,[(1,2),(1,2,2),(2,-2),(1,-2)],[1])==(1,16)
check(4,[(),(1,-1),(),(2,2)],[])
check(0,[],[])
check(0,[()],[])
for cap in (0,1,2):
    p=impl.project(3,[(1,3),(2,3),(-3,)],cover=[1,2],pair_cap=cap)
    assert (p is None) if cap<2 else p.pairs==2
for n,rows,cover in [(3,[(1,2)],[]),(2,[(0,)],[1]),(2,[(3,)],[])]:
    try:
        impl.project(n,rows,cover=cover)
    except ValueError:
        continue
    raise AssertionError('invalid input accepted')
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(**stats,checker=digest(__file__),target=digest(impl.__file__),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
