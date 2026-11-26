from pathlib import Path
from unittest.mock import patch
import runpy
here=Path(__file__).resolve().parent
def local(kind,flags):
    if kind=='triangle':
        a,b,c=flags
        return a and b and c,a or b
    if len(flags)==4:
        a,b,c,d=flags
        return (a and c) or (b and d),b or c
    a,b,c,d,e=flags
    return (c and (a or e)) or (b and d),b or d
for prefix,first,second,cap in [('triangle-p4','triangle',4,4),('p4-p4','path',4,5),('p4-p5','path',5,6)]:
    h=3 if first=='triangle' else 4;n=h+second
    es=[(i,i+1) for i in range(h-1)]+([(0,h-1)] if first=='triangle' else [])+[(i,i+1) for i in range(h,n-1)]
    for selected in range(1<<len(es)):
        flags=[False]*n
        for i,(a,b) in enumerate(es):
            if selected>>i&1:flags[a]=flags[b]=True
        x,p=local(first,flags[:h]);y,q=local('path',flags[h:])
        assert (x or y or (p and q))==(selected.bit_count()>=2)
    mask=sum(1<<(b*(b-1)//2+a) for a,b in es)
    class Capture:
        def __init__(self,**kw):self.clauses=[]
        def add_clause(self,c):self.clauses.append(c)
        def solve(self):
            lim=max(abs(v) for c in self.clauses for v in c)
            (here/(prefix+'.cnf')).write_text(f'p cnf {lim} {len(self.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in self.clauses))
            return True
        def delete(self):pass
    with patch('pysat.solvers.Cadical195',Capture):
        mod=runpy.run_path(str(here.parents[2]/'degree/t13-seven/graph-cut/cert.py'))
    mod['check'](n,mask,cap)
    print(prefix,'vertices',n,'mask',mask,'cap',cap,'control ORs',cap+1,'raw tests',1<<len(es))
