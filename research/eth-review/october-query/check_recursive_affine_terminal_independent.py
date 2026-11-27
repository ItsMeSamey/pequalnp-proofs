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
from affine_packet_terminal_v2 import LinearEntry,AffineTerminal,TerminalCap
import variable_packet_machine_affine as actual, variable_packet_machine as old
from multilevel_packet_machine import Table
from packet_entry_tape import canonical_lift
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(actual.__file__)=='64636c189e112b4b2b6f22f57517b9ac4af2019091e2dded9810173d7bba6d1b'
import affine_packet_terminal_v2 as term
assert sha(term.__file__)=='2d0c9ea83a3ed8226a1e930a174a2767d3b031ddd7d5c22ad3bdc7ee85fbed19'
f=(1,1)
ring=actual.Ring(4,f,2)
leaf=lambda *args:None
def plan(net,m,depth):
    return None if depth else (1,1,((0,None),),[([0],[1])])
visits=[]
outputs=[]
for bit in (0,1):
    lin=LinearEntry(1,((1,bit),),2,4)
    data=Table(3,((7,5,0,1),(2,0,3,6)))
    nw=(((lin,(0,)),),((data,(0,)),))
    aff=AffineTerminal(10000)
    def terminal(net,m,r):
        descs=[d for side in net for d,ps in side]
        assert any(isinstance(d,actual.Description) and d.birth>4 for d in descs)
        visits.append(tuple(d.birth for d in descs))
        value=aff(net,m,r)
        assert value==actual.solve(net,m,r.p,f,2,0,leaf)
        return value
    value=actual.solve(nw,1,4,f,2,0,plan,terminal)
    assert value==old.solve(nw,1,4,f,2,0,plan)==canonical_lift(data.word((bit,)),3,4)
    assert aff.stats['max_support_rank']==1 and aff.stats['states']>0
    outputs.append(value)
impossible=LinearEntry(2,((3,1),),3,4)
assert AffineTerminal(0)((((impossible,(0,0)),),()),1,ring)==ring.scalar(0)
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),targets=[sha(x.__file__) for x in (actual,term)],descendant_checks=len(visits),outputs=outputs,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
