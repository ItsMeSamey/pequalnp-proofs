from time import perf_counter
from affine_packet_terminal_v2 import AffineTerminal,LinearEntry,TerminalCap,rs_first
from variable_packet_machine_affine import solve,Description,Ring
from rs_coset_entries import Network
from source_cnf_driver import Predicate

f=(1,1)
plan=lambda *args:None
net=Network(4)
p=12
ell=2
root=rs_first(net,5,4)
m=root.arity
# Actual one-mode source-only packet entry: positions y=2j in L=64,
# residue 0, step 2, moment b=1 and source exponent 1.
packet=Description(Ring(5,f,ell),(),m,(),((tuple(range(m)),1),))
ports=tuple(range(m))
network=(((root,ports),),((packet,ports),))
start=perf_counter()
term=AffineTerminal(256)
out=solve(network,m,p,f,ell,0,plan,term)
duration=perf_counter()-start
expected=0
for input_word in range(256):
    a,b=input_word&15,input_word>>4
    outputs=[a^net.mul(b,t) for t in net.constants]
    w=input_word|sum(x<<(8+4*j) for j,x in enumerate(outputs))
    expected+=sum(j for j in range(24) if w>>j&1)%32
assert out==Ring(p,f,ell).scalar(expected)
assert term.stats['states']==256 and term.stats['max_support_rank']==16
small=LinearEntry(3,((3,1),),4,4)
rr=Ring(3,f,ell)
# Nonzero V and extension coefficients with negative local entries at birth.
res=Description(rr,((((7,1,3,2),),()),),1,(),())
copy=Predicate('copy',(),4,4)
tiny=(((small,(0,1,2)),),((res,(0,1)),(copy,(2,))))
old=solve(tiny,3,9,f,ell,0,plan)
t=AffineTerminal(2)
assert solve(tiny,3,9,f,ell,0,plan,t)==old
assert t.stats['states']==2 and t.stats['max_free']==2
assert solve(tiny,3,9,f,ell,0,plan,AffineTerminal(0,direct_fallback=True))==old
try: solve(tiny,3,9,f,ell,0,plan,AffineTerminal(0))
except TerminalCap: pass
else: raise AssertionError('cap missed')
# Local masks may duplicate real coordinates (standalone terminal).
impossible=LinearEntry(2,((3,1),),4,4)
assert AffineTerminal(0)((((impossible,(0,0)),),()),1,rr)==rr.scalar(0)
assert AffineTerminal(0)(((),()),4,rr)==rr.scalar(0)
print('PASS RS first gate:',m,'wires, projected states',term.stats['states'],
      'ambient',1<<m,'ring output',out,'elapsed seconds',round(duration,6),
      '; affine projected fiber, mixed birth/V, duplicate cancellation and cap controls')
empty=((((Predicate('copy',(),3,4),()),(LinearEntry(0,(),3,4),())),()),)
# A normal two-shore graph, with two zero-port vertices on the first shore.
empty=empty[0]
assert solve(empty,0,3,f,ell,0,plan,AffineTerminal(1))==rr.scalar(1)
assert solve(empty,0,3,f,ell,0,plan)==rr.scalar(1)
try: AffineTerminal(5)((((copy,(1,)),),()),1,rr)
except ValueError: pass
else: raise AssertionError('invalid physical edge accepted')
print('PASS empty COPY/affine graph and out-of-range physical edge rejection')
