"""Test the necessary twelve-signature cover by two witnesses for each signed port."""
from pathlib import Path
from itertools import combinations
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from sys import argv

def signatures(t):
    result=set()
    for s in range(128):
        m=0
        for j in reversed(range(7)):
            if j>=len(t) or (m&t[j]):m|=1<<(2*j+((s>>j)&1))
        result.add(m)
    return sorted(result)

def exists_cover(t):
    masks=signatures(t)
    if len(masks)<12:return False
    port=[[i+1 for i,m in enumerate(masks) if (m>>j)&1] for j in range(14)]
    if min(map(len,port))<2:return False
    cnf=CardEnc.atmost(range(1,len(masks)+1),bound=12,encoding=EncType.seqcounter)
    for p in port:
        # At least two from this port: for each excluded one choose another.
        for j in p:cnf.append([k for k in p if k!=j])
    with Solver(name='cadical195',bootstrap_with=cnf.clauses) as s:return s.solve()

if __name__=='__main__':
    for line in Path(argv[1]).read_text().splitlines():
        i,c,cap,*t=map(int,line.split())
        assert cap==len(signatures(t))
        print(i,c,cap,int(exists_cover(t)))
