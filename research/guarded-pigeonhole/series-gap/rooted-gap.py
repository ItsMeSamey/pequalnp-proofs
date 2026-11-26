"""Independent raw ordinary PC check for a rooted affine gap, with explicit square axioms."""
from itertools import combinations_with_replacement
from functools import lru_cache
from collections import deque
import sys
PREVIOUS=[8398,785,9,8469,8490,1040,10369,1089,9754,8450,4512,4160,3072,857]
EXAMPLE=[1550,401,9,2197,2218,1232,2720,3450,2178,2113,2209,2008]
@lru_cache(None)
def ring(n,d):
    mons=[m for k in range(d+1)for m in combinations_with_replacement(range(n),k)]
    pos={m:i for i,m in enumerate(mons)}
    low=sum(len(p)<d for p in mons)
    mul=[[1<<pos[tuple(sorted(m+(j,)))] for m in mons[:low]] for j in range(n)]
    return pos,low,mul
def reduce(p,b):
    while p and p.bit_length() in b:p^=b[p.bit_length()]
    return p
def prove(rows,d,opp,weight=4,rhs=0):
    n=len(rows);pos,low,mul=ring(n,d)
    todo=deque();basis={};form=rhs^sum(1<<pos[(i,)] for i in range(n) if weight>>i&1);target=1 if opp else form
    for i,v in enumerate(rows):
        assert all((rows[j]>>i&1)==(v>>j&1) for j in range(n)) and not(v>>i&1)
        todo.append((1<<pos[(i,i)])^(1<<pos[(i,)]))
        p=0
        for j in range(n):
            if v>>j&1:p^=1<<pos[tuple(sorted((i,j)))]
        todo.append(p)
    for j in [0,1]:todo.append(1^(1<<pos[(j,)]))
    if opp:todo.append(1^form)
    while todo:
        p=reduce(todo.popleft(),basis)
        if not p:continue
        k=p.bit_length();basis[k]=p
        if k<=n+1 and not reduce(target,basis):return True,len(basis)
        if k<=low:
            supp=[]
            while p:
                bit=p&-p;p^=bit;supp.append(bit.bit_length()-1)
            for mx in mul:
                z=0
                for j in supp:z^=mx[j]
                todo.append(z)
    return not reduce(target,basis),len(basis)
def modelcheck(rows):
    sol=[x for x in range(3,1<<len(rows),4)
         if all(not(x>>v&1) or (nb&x).bit_count()%2==0 for v,nb in enumerate(rows))]
    assert sol and not any(x&4 for x in sol)
    colors={}
    def color(v,c):
        if v in colors:return colors[v]==c
        colors[v]=c
        return all(color(j,1-c) for j in range(len(rows)) if rows[v]>>j&1)
    return len(sol),all(color(j,0)for j in range(len(rows))if j not in colors)
if __name__=='__main__':
    rows=list(map(int,sys.argv[1:])) if len(sys.argv)>1 else EXAMPLE
    print('Models and bipartiteness:',modelcheck(rows),flush=True)
    for d in (2,3,4):
        for opp in (False,True):
            print('Raw degree',d,'refute opposite' if opp else 'derive fixed bit',prove(rows,d,opp),flush=True)
