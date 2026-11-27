"""Free-OR feasibility for a fixed actual leak set of the three-sink terminal."""
from itertools import combinations
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver
from h5_raw_terminal import EDGES,target
N=[x for x in range(1024) if not target(x) and all(target(x|1<<i) for i in range(10) if not x>>i&1)]
CASES=tuple(combinations(range(16),2))+tuple(combinations(range(16),3))
def formula(ids):
    pool=IDPool();cnf=CNF();t=pool.id();cnf.append([t])
    def meet(xs):
        if not xs:return t
        if len(xs)==1:return xs[0]
        y=pool.id()
        for x in xs:cnf.append([-y,x])
        cnf.append([y]+[-x for x in xs]);return y
    def join(xs):return -meet([-x for x in xs])
    pairs=[[[pool.id() for _ in range(k)] for _ in range(2)] for k in (10,11,12,12,12)]
    um=[pool.id(),pool.id()];vm=[pool.id(),pool.id()]
    cnf.append(um)
    for x,y in zip(um,vm):cnf.append([-x,-y])
    for i in (0,1):
        cnf.append([op[10+i] for pair in pairs[i+1:] for op in pair if len(op)>10+i])
    union=0
    for i in ids:union|=N[i]
    rmask=1023^union
    pos=[];neg=[];uc=[]
    for j,x in enumerate(list(EDGES)+N):
        h=[]
        for pair in pairs:
            two=[]
            for op in pair:
                pieces=[op[i] for i in range(10) if x>>i&1]
                pieces.extend(meet([s,v]) for s,v in zip(op[10:],h))
                two.append(join(pieces))
            h.append(meet(two))
        u=join(([t] if x&rmask else [])+[meet([s,v]) for s,v in zip(um,h)])
        residual=[meet([s,v]) for s,v in zip(vm,h)]
        v=join(residual+h[2:])
        if j<13:
            cnf.append([u]);cnf.append([v]);pos.append((h,residual))
        else:
            is_leak=j-13 in ids;cnf.append([v if is_leak else -v])
            if is_leak:cnf.append([-u])
            neg.append(h);uc.append(u)
    # An actual P has size <=3 in the remaining sectors; saturating R only shrinks P.
    other=[uc[i] for i in range(16) if i not in ids]
    for row in combinations(other,4-len(ids)):cnf.append(list(row))
    for i in range(5):
        cnf.append([h[i] for h,_ in pos]);cnf.append([h[i] for h in neg])
    choices=[]
    for k in range(3):
        z=[]
        for h,v in pos:
            w=pool.id();z.append(w)
            for lit in [h[k+2]]+[-h[j+2] for j in range(3) if j!=k]+[-a for a in v]:
                cnf.append([-w,lit])
        cnf.append(z);choices.append(z)
    for a,b in zip(choices,choices[1:]):
        for i,c in enumerate(a):
            for d in b[:i+1]:cnf.append([-c,-d])
    return cnf,pairs,um,vm,rmask

def probe(index,budget):
    ids=CASES[index]
    cnf,pairs,um,vm,r=formula(ids)
    with Solver(name='g4',bootstrap_with=cnf.clauses) as solver:
        solver.conf_budget(budget)
        ans=solver.solve_limited()
        if ans:
            m=set(solver.get_model())
            mask=lambda xs:sum(1<<i for i,a in enumerate(xs) if a in m)
            gates=[tuple(mask(a) for a in pair) for pair in pairs]
            u=r|(mask(um)<<10);v=(mask(vm)<<10)|(7<<12)
            for x in range(1024):
                wire=x
                for j,(a,b) in enumerate(gates):
                    if wire&a and wire&b:wire|=1<<(10+j)
                assert bool(wire&u and wire&v)==target(x)
            return 'SAT',gates,u,v
        return ('UNSAT' if ans is False else 'UNKNOWN',)
if __name__=='__main__':
    import sys
    for index in map(int,sys.argv[2:]):
        print(index,CASES[index],probe(index,int(sys.argv[1])),flush=True)
