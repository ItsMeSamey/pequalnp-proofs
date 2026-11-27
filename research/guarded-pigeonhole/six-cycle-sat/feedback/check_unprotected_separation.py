"""Smallest connected fixed-count unprotected example and the variable-count cap trap."""
from itertools import combinations

def cycles(p):
    seen=set();out=[]
    for i in range(len(p)):
        if i in seen:continue
        cyc=[]
        while i not in seen:
            seen.add(i);cyc.append(i);i=p[i]
        out.append(tuple(cyc))
    return tuple(out)

def routing(fb, gates, mask):
    local=list(range(len(fb)))
    for i,g in enumerate(gates):
        if mask>>i&1:
            for j,v in enumerate(g):local[v]=g[(j+1)%len(g)]
    return [fb[v] for v in local]

def compose(f,g):
    return [f[x] for x in g]

fb=(0,1,3,4,5,2)
gate=((0,3,2),(1,5,4))
states=[cycles(routing(fb,gate,m)) for m in range(4)]
assert all(len(s)==3 for s in states)
def separate(S):
    return all(all(len(set(C)&set(S))<=1 for C in s) for s in states)
E=[p for p in combinations(range(6),2) if separate(p)]
assert (1,5) in E and not any(separate(p) for p in combinations(range(6),3))
connected={0}
while True:
    S=connected|{fb[v] for v in connected}|{v for g in gate if set(g)&connected for v in g}
    if S==connected:break
    connected=S
assert len(connected)==6
tau=(1,2,0);inv=(2,0,1)
var=[routing(range(3),((0,1,2),),m) for m in range(2)]
assert [len(cycles(p)) for p in var]==[3,1]
assert [len(cycles(compose(tau,p))) for p in var]==[1,1]
assert [len(cycles(compose(inv,p))) for p in var]==[1,3]
print('fixed-count states:',states,'always-separated pairs:',E)
print('variable-count original 3,1; fixed cap 1,1; inverse cap 1,3')
