"""Restrict to pure--pure labels. Synthesize both partner ports and threshold output using one shared OR budget, allowing free arbitrary conjunctions."""
from itertools import combinations
from pathlib import Path
import sys
from pysat.solvers import Cadical195
from pysat.formula import IDPool
from probe_sat_strong import jobs

def profile(common,rows):
    pure=sorted((tag,partner) for tag,partner in rows if tag.bit_count()==2)
    positives=sorted({a|b for (a,_),(b,_) in combinations(pure,2)})
    tests=[(a,0,p) for a,p in pure]+[(a,1,None) for a in positives]
    return common,tuple(tests)

def check(common,tests,budget=4):
    names=IDPool()
    with Cadical195() as sat:
        def product(slot,t,mask,previous):
            bad=[names.id(('falseInput',slot))]
            for j in range(6+len(previous)):
                use=names.id(('use',slot,j))
                if j<6:
                    if not (mask>>j)&1:bad.append(use)
                else:
                    y=previous[j-6]
                    v=names.id(('bad',slot,t,j))
                    sat.add_clause([-v,use]);sat.add_clause([-v,-y]);sat.add_clause([v,-use,y]);bad.append(v)
            result=names.id(('product',slot,t))
            for b in bad:sat.add_clause([-result,-b])
            sat.add_clause([result,*bad])
            return result
        for t,(mask,out,partners) in enumerate(tests):
            wires=[]
            for i in range(budget):
                x=product(2*i,t,mask,wires);y=product(2*i+1,t,mask,wires)
                z=names.id(('sum',i,t));sat.add_clause([-x,z]);sat.add_clause([-y,z]);sat.add_clause([x,y,-z])
                wires.append(z)
            outwire=product(2*budget,t,mask,wires)
            sat.add_clause([outwire if out else -outwire])
            if partners is not None:
                for i in range(1 if common else 2):
                    z=product(2*budget+1+i,t,mask,wires)
                    sat.add_clause([z if partners>>i&1 else -z])
        sat.conf_budget(2000)
        return sat.solve_limited()

if __name__=='__main__':
    data=sorted({profile(c,r) for c,r in jobs(Path(sys.argv[1]))},key=repr)
    print('profiles',len(data),flush=True)
    for i,p in enumerate(data):
        print(i,check(*p),flush=True)
