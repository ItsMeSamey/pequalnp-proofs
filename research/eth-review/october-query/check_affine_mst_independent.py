"""Independent physical-assignment controls for two automatic discovery APIs."""
import os,fcntl,hashlib,itertools,json,resource,signal
from pathlib import Path
lk='/workspace/scratch/pnp-native-search.lock'
handle=open(lk,'a')
def inode(s): return (s.st_dev,s.st_ino)
key=inode(os.fstat(handle.fileno()))
assert key==inode(os.stat(lk))
fcntl.flock(handle,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert key==inode(os.stat(lk))
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import affine_mst_cnf as mst, signed_cover_projection as signed
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(mst.__file__)=='e6d5aa84c0256b07cacec22bf90a3ccb68f07c689225b558c41a63338ae9de98'
assert sha(signed.__file__)=='37cc4e33a052b0bfa17917e077249e40fcd344df148876164e0105915d72aeee'
def sat(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)
stats=dict(fixtures=0,raw_models=0,compact_words=0,nontrivial_trees=0,unsat=0)
def check(n,rows):
    c=mst.compile(n,rows,scope_cap=n,table_cap=10000)
    raw={x for x in range(1<<n) if sat(rows,x)}
    ygroups={}
    for x in raw:
        y=tuple((x&b).bit_count()%2 for b in c.basis)
        ygroups.setdefault(y,set()).add(x)
    seen=set()
    for w in range(1<<len(c.tree)):
        y=[0]*len(c.basis)
        for j,edge in enumerate(c.tree):
            for i in edge:
                if i: y[i-1]^=(w>>j)&1
        key=tuple(y)
        assert key not in seen
        seen.add(key)
        g=ygroups.get(key,set())
        assert sat(c.clauses,w)==bool(g)
        witness=c.lift(w)
        if g: assert len(g)==c.fiber and witness in g
        else: assert witness is None
    assert seen.issuperset(ygroups)
    stats['fixtures']+=1
    stats['raw_models']+=len(raw)
    stats['compact_words']+=len(seen)
    stats['nontrivial_trees']+=any(a*b for a,b in c.tree)
    stats['unsat']+=not raw
def forbidden(variables,w):
    return tuple(-v if w>>j&1 else v for j,v in enumerate(variables))
for mask in range(256):
    rows=[forbidden([3,1,4],j) for j in range(8) if mask>>j&1]
    if mask%2: rows.extend([(-3,2),(-3,2),(5,-5),(-2,-2,4)])
    check(6,rows)
for a,b in itertools.product((0,1),repeat=2):
    rows=[forbidden(ids,w) for ids,t in [([4,1,2],a),([5,3,2],b)] for w in range(8) if w.bit_count()%2==t]
    for extra in ([],[(1,-5,6),(-4,6),(5,-6)],[(1,),(-1,)], [()]):
        check(7,rows+extra)
for width,table in [(0,100),(3,0)]:
    assert mst.compile(3,[(1,2,3)],scope_cap=width,table_cap=table) is None
import affine_mst_complete as complete
assert sha(complete.__file__)=='86c01fd163acf614ab2eaa4b1df7561f2f2720ac82806e29644d9eecc0156b70'
offset=[(1,2),(-1,-2),(1,3)]
def checked_solve(rows,ids,words,route,callback=None):
    raw=[w for w in range(32) if sat(rows,w)]
    r=complete.solve(5,rows,scope_cap=5,table_cap=100,chart_word_cap=words,
                     observable_ids=ids,original_backend=callback)
    assert r['route']==route and r['count']==len(raw) and r['witness'] in raw
checked_solve(offset,(2,3),32,'supplied')
checked_solve(offset,(1,2),32,'automatic')
checked_solve(offset,(2,3),0,'original-exhaustive')
def cb(n,rows):
    assert n==5 and list(rows)==offset
    sols=[w for w in range(32) if sat(rows,w)]
    return len(sols),sols[-1]
checked_solve(offset,(2,3),0,'original-backend',cb)
taut=[forbidden((1,2,3,4),w) for w in range(16) if w.bit_count()%2==0]+[(-4,),(1,2,3)]
chart=complete.compile(5,taut,scope_cap=0,table_cap=0)
assert chart is not None and chart.tree==() and not chart.clauses and chart.fiber==8
assert sat(taut,chart.lift(0))
import affine_mst_backend as shared
assert sha(shared.__file__)=='74efa08c72734896238ef06090ceb85e0e47dc322f6642a66c462cab6b2aa948'
for decline in (False,True):
    calls=[]
    def count_only(n,rows):
        calls.append((n,len(rows)))
        if decline and n<5: return NotImplemented
        return sum(sat(rows,w) for w in range(1<<n))
    r=shared.solve(5,offset,scope_cap=5,table_cap=100,backend=count_only)
    assert r['route']==('original' if decline else 'automatic')
    assert r['count']==sum(sat(offset,w) for w in range(32)) and sat(offset,r['witness'])
    assert calls==[(d,n) for _,d,n,_ in r['calls']] and max(p for *_,p in r['calls'])>=2
try:
    shared.solve(5,offset,scope_cap=5,table_cap=100,backend=lambda d,cs:(1,1<<d))
except ValueError: pass
else: raise AssertionError('accepted invalid witness')
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(**stats,checker=sha(__file__),targets=[sha(m.__file__) for m in (mst,complete,shared)],rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
