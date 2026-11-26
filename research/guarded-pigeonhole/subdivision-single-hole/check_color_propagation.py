from itertools import combinations
from collections import deque
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'pc-degree'))
from check import ring

def run(n,E,pin,target,d):
    pos,low,mults=ring(2*n,d)
    forms=[({1<<(2*i)},{1<<(2*i+1)},{0,1<<(2*i),1<<(2*i+1)}) for i in range(n)]
    def product(A,B):
        p=0
        for a in A:
            for b in B:p^=1<<pos[a|b]
        return p
    def vec(A):return sum(1<<pos[a] for a in A)
    q=deque(product(v[0],v[1]) for v in forms)
    for a,b in E:q.extend(product(x,y) for x,y in zip(forms[a],forms[b]))
    for v,c in pin:q.append(vec(forms[v][c])^1)
    piv={}
    def reduce(x):
        while x and x.bit_length() in piv:x^=piv[x.bit_length()]
        return x
    goal=1 if target is None else vec(forms[target[0]][target[1]])^1
    while q:
        x=reduce(q.popleft())
        if not x:continue
        piv[x.bit_length()]=x
        if not reduce(goal):return True
        if x.bit_length()>low:continue
        terms=[]
        while x:
            a=x&-x;terms.append(a.bit_length()-1);x-=a
        for mul in mults:
            y=0
            for j in terms:y^=mul[j]
            q.append(y)
    return False

if __name__=='__main__':
    clique=list(combinations(range(4),2))
    fixtures=[('K4',4,clique,[],None),('K4 pinned',4,clique,[(0,0)],None),('diamond equality',4,clique[1:],[(0,0)],(1,0))]
    for k in (3,5):
        edges=[(i,(i+1)%k) for i in range(k)]+[(i,k) for i in range(k)]
        fixtures += [(f'wheel{k} rooted',k+1,edges,[(k,0)],None),(f'wheel{k} deletion',k+1,edges[1:],[(0,0)],(1,0))]
    for name,n,E,p,g in fixtures: print(name,[run(n,E,p,g,d) for d in (2,3,4)],flush=True)
