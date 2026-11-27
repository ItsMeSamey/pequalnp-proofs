"""One common bank of six OR helpers, plus eight distinct sink unions."""
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver
def encode(targets,limit):
    sub=set()
    for options in targets:
        for x in options:
            y=x
            while y:
                if y!=x and y.bit_count()>=2:sub.add(y)
                y=(y-1)&x
    pins={1<<j for j in range(9)}
    pool=IDPool();f=CNF();selected={s:pool.id(('bank',s)) for s in sorted(sub)}
    f.extend(CardEnc.atmost(list(selected.values()),limit,vpool=pool,encoding=EncType.seqcounter).clauses)
    def decomps(x):
        vals=sorted(y for y in pins|sub if y!=x and y&x==y)
        ans=[]
        for a,b in combinations(vals,2):
            if a|b!=x:continue
            if a in pins and b in pins:return None
            if a in pins or b in pins:ans.append(selected[b if a in pins else a]);continue
            ab=pool.id(('and',a,b))
            f.append([-ab,selected[a]]);f.append([-ab,selected[b]])
            ans.append(ab)
        return ans
    for x,p in selected.items():
        c=decomps(x)
        if c is not None:f.append([-p]+c)
    for options in targets:
        possible=[decomps(x) for x in options]
        if None not in possible:f.append([q for c in possible for q in c])
    return f,selected
def instance(fullrow,limit):
    # tail signs O,T,P,M,H0,H1 hit semantic 3x2 states
    states=[(r,h) for r in range(3) for h in range(2)]
    active=[(r,h) for r,h in states if r==fullrow or h==0]
    signs=[{(r,h) for r,h in states if test(r,h)} for test in
        (lambda r,h:r==0,lambda r,h:r!=0,lambda r,h:r==1,lambda r,h:r==2,
         lambda r,h:h==0,lambda r,h:h==1)]
    targets=[]
    for r,h in active:
        opts=[]
        for mask in range(64):
            accepted=set().union(*(v for j,v in enumerate(signs) if mask>>j&1))
            if accepted==set(states)-{(r,h)}:opts.append(mask<<3)
        for side in (1,2):targets.append([4|side|m for m in opts])
    formula,sel=encode(targets,limit)
    stem='ternary-'+str(fullrow)+'-'+str(limit)
    formula.to_file('/dev/shm/'+stem+'.cnf')
    with Solver(name='g4',bootstrap_with=formula.clauses,with_proof=True) as solver:
        result=solver.solve()
        print(stem,'target-option-counts',list(map(len,targets)),'clauses',len(formula.clauses),'SAT',result,flush=True)
        if result:
            model=set(solver.get_model())
            bank={v for v,k in sel.items() if k in model}
            wires={1<<j for j in range(9)}
            for v in sorted(bank,key=int.bit_count):
                assert any(a|b==v for a,b in combinations(wires,2));wires.add(v)
            assert all(any(a|b in options for a,b in combinations(wires,2)) for options in targets)
            print('bank',sorted(bank),flush=True)
        else:Path('/dev/shm/'+stem+'.drat').write_text('\n'.join(solver.get_proof())+'\n')
if __name__=='__main__':
    import sys
    for s in sys.argv[1:]:
        r,k=map(int,s.split(','));instance(r,k)
