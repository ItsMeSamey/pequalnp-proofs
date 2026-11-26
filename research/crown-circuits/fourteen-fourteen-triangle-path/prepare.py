"""Instantiate the archived AND-cone encoding without launching its solver."""
from pathlib import Path
from itertools import combinations
from unittest.mock import patch
import runpy
here=Path(__file__).resolve().parent
edges=[(0,1),(1,2),(2,0),(3,4),(4,5),(5,6),(6,7)]
mask=sum(1<<(max(a,b)*(max(a,b)-1)//2+min(a,b)) for a,b in edges)
def control(x):
    a,b,c,p,q,r,s,t=[bool(x>>i&1) for i in range(8)]
    return (a and b and c) or ((r and (p or t)) or (q and s)) or ((a or b) and (q or s))
for choice in range(128):
    x=0
    for i,(a,b) in enumerate(edges):
        if choice>>i&1:x|=1<<a|1<<b
    assert control(x)==(choice.bit_count()>=2)
# Capture precisely the clauses passed to the published encoder's SAT backend.
class Capture:
    def __init__(self,**kw):self.clauses=[]
    def add_clause(self,c):self.clauses.append(c)
    def solve(self):
        n=max(abs(v) for c in self.clauses for v in c)
        (here/'graph.cnf').write_text(f'p cnf {n} {len(self.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in self.clauses))
        return True
    def delete(self):pass
with patch('pysat.solvers.Cadical195',Capture):
    mod=runpy.run_path(str(here.parents[2]/'degree/t13-seven/graph-cut/cert.py'))
mod['check'](8,mask,5)
print('mask',mask,'6-OR upper control passed 128/128; 5-OR CNF generated')
