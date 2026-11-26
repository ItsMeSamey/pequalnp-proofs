"""Full raw uneliminated degree-three PC check on the 38-vertex series graph."""
from pathlib import Path
import runpy
from collections import deque
pkg=Path(__file__).parent
raw=runpy.run_path(str(pkg/'rooted-gap.py'))
bip=runpy.run_path(str(pkg/'rooted-bipartite-gap.py'))
def instance():
    h=bip['graph'];n=len(h)
    G=h.copy()+[a<<n for a in h]
    def flip(a,b):G[a]^=1<<b;G[b]^=1<<a
    flip(0,1);flip(n,n+1);flip(0,n+1);flip(1,n)
    return G,[1,1<<(n+1),bip['weight']|(bip['weight']<<n)]
def fullcheck(d,strong=False):
    G,forms=instance();n=len(G)
    if strong:forms+=[1<<1,1<<(n//2)]
    pos,low,mul=raw['ring'](n,d)
    todo=deque();basis={}
    for i,row in enumerate(G):
        todo.append((1<<pos[(i,)])^(1<<pos[(i,i)]))
        todo.append(sum(1<<pos[tuple(sorted((i,j)))] for j in range(n) if row>>j&1))
    for row in forms:todo.append(1^sum(1<<pos[(i,)] for i in range(n) if row>>i&1))
    while todo:
        p=raw['reduce'](todo.popleft(),basis)
        if not p:continue
        if p==1:return True,len(basis)+1
        k=p.bit_length();basis[k]=p
        if k<=low:
            support=[]
            while p:
                b=p&-p;p^=b;support.append(b.bit_length()-1)
            for mx in mul:
                z=0
                for j in support:z^=mx[j]
                todo.append(z)
    return False,len(basis)
if __name__=='__main__':
    for s in (False,True):
        print("Strong" if s else "Weak",fullcheck(3,s),flush=True)
