"""Punctured Fano finite synthesis. Optional argument: output 20-gate DIMACS."""
import sys
from itertools import combinations, product
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver
points=[v for v in range(1,8) if v!=1]
lines=[v for v in range(1,8) if v!=2]
edges={(i,6+j) for i,p in enumerate(points) for j,l in enumerate(lines)
       if (p&l).bit_count()%2==0}
def masks(lo):
    return [set(c) for k in range(3) for c in combinations(range(lo,lo+6),k)]
tests=[({i,j},True) for i,j in sorted(edges)]
tests += [(a|b,False) for a,b in product(masks(0),masks(6))
          if not any(i in a and j in b for i,j in edges)]
gates=[]
def add(op,a,b):
    gates.append((op,*sorted((a,b))))
    return 11+len(gates)
def collect(xs):
    a,*rest=xs
    for b in rest: a=add('or',a,b)
    return a
collect([add('and',p,collect(sorted(j for i,j in edges if i==p))) for p in range(6)])
assert len(gates)==21 and len(edges)==16
for m in range(4096):
    val=[bool(m>>i&1) for i in range(12)]
    for op,a,b in gates: val.append((val[a] and val[b]) if op=='and' else (val[a] or val[b]))
    assert val[-1]==any(val[i] and val[j] for i,j in edges)
def encode(size):
    ids,cnf=IDPool(),CNF()
    def v(*key): return ids.id(key)
    for t,(mask,pos) in enumerate(tests):
        for j in range(12): cnf.append([v(j,t) if j in mask else -v(j,t)])
        cnf.append([v(11+size,t) if pos else -v(11+size,t)])
    for i in range(12,12+size):
        for s in (0,1):
            choices=[v('p',i,s,j) for j in range(i)]
            cnf.append(choices)
            for a,b in combinations(choices,2): cnf.append([-a,-b])
        for t in range(len(tests)):
            a,b,o,kind=v('a',i,0,t),v('a',i,1,t),v(i,t),v('and',i)
            for s,z in enumerate((a,b)):
                for j in range(i):
                    q,y=v('p',i,s,j),v(j,t)
                    cnf.extend([[-q,-z,y],[-q,z,-y]])
            cnf.extend([[-kind,-o,a],[-kind,-o,b],[-kind,-a,-b,o],
                        [kind,-a,o],[kind,-b,o],[kind,-o,a,b]])
    return cnf,v
cnf,v=encode(21)
pins=[]
for i,(op,a,b) in enumerate(gates,12):
    pins.extend([v('and',i) if op=='and' else -v('and',i),v('p',i,0,a),v('p',i,1,b)])
with Solver(name='g3',bootstrap_with=cnf) as sol: assert sol.solve(assumptions=pins)
if len(sys.argv)==2: encode(20)[0].to_file(sys.argv[1])
print('16 flags,',len(tests)-16,'negatives; 4096 full-cube checks and pinned SAT witness passed')
