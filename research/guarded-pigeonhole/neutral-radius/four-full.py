"""Independent ordinary PC closure for unresolved maximal four-left type sets."""
from collections import deque
from functools import lru_cache
from itertools import combinations
import sys

@lru_cache(None)
def ring(n,d):
    mons=[sum(1<<i for i in a) for k in range(d+1) for a in combinations(range(n),k)]
    index={m:i for i,m in enumerate(mons)}
    low=sum(m.bit_count()<d for m in mons)
    images=[[1<<index[m|1<<v] for m in mons[:low]] for v in range(n)]
    return index,low,images

def refutes(labels, rows):
    n=len(labels)
    index,low,images=ring(n,3)
    todo=deque()
    for i,row in enumerate(rows):
        p=0
        for j in range(n):
            if row>>j&1:p^=1<<index[(1<<i)|(1<<j)]
        todo.append(p)
    for j in range(3):
        p=int(j==2)
        for v,l in enumerate(labels):
            if l>>j&1:p^=1<<index[1<<v]
        todo.append(p)
    basis={}
    while todo:
        p=todo.popleft()
        while p:
            lead=p.bit_length()-1
            if lead in basis:
                p^=basis[lead]
                continue
            if lead==0:return True
            basis[lead]=p
            if lead<low:
                terms=[]
                while p:
                    b=p&-p;p^=b;terms.append(b.bit_length()-1)
                for mult in images:
                    product=0
                    for k in terms:product^=mult[k]
                    todo.append(product)
            break
    return False

def decode(line):
    *head,mask=line.split()
    left=list(map(int,head))
    tset=int(mask,16)
    types=[t for t in range(64) if tset>>t&1]
    rows=[0]*4+[t//4 for t in types]
    labels=left+[t%4 for t in types]
    for y,t in enumerate(types,4):
        for i in range(4):
            if (t//4)>>i&1:rows[i]|=1<<y
    return labels,rows

if __name__=='__main__':
    n=0
    for line in open(sys.argv[1]):
        labels,rows=decode(line)
        if not refutes(labels,rows):
            print("Unresolved",line,flush=True)
            raise SystemExit(1)
        n+=1
    print(f"All {n} maximal instances refuted by full ordinary PC degree three.")
