"""Four charged binary ORs, two prescribed single-use private ANDs and free ordinary conjunctions after pure-edge specialization."""
from partner_budget import profile,jobs
from pathlib import Path
import sys
from pysat.formula import IDPool
from pysat.solvers import Cadical195

def check(common,tests,loads,conflicts=30000,certificate=None):
    names=IDPool()
    with Cadical195(with_proof=certificate is not None) as s:
        clauses=[]
        def emit(clause):
            if certificate is not None:clauses.append(clause)
            s.add_clause(clause)
        def exactly_one(xs):
            emit(xs)
            for j,x in enumerate(xs):
                for y in xs[:j]:emit([-x,-y])
        types=[[names.id(('type',i,k)) for k in range(3+len(loads))] for i in range(6+len(loads))]
        for row in types:exactly_one(row)
        for k in range(1,3+len(loads)):exactly_one([row[k] for row in types])
        def prod(slot,t,base,prev):
            penalties=[names.id(('falseInput',slot))]
            for j,v in enumerate([*base,*prev]):
                use=names.id(('use',slot,j))
                if v is False:penalties.append(use)
                elif v is not True:
                    b=names.id(('bad',slot,t,j))
                    emit([-b,use]);emit([-b,-v]);emit([b,-use,v]);penalties.append(b)
            r=names.id(('prod',slot,t))
            for b in penalties:emit([-r,-b])
            emit([r,*penalties]);return r
        for t,(mask,want,partners) in enumerate(tests):
            base=[bool(mask&(1<<i)) for i in range(4)]
            prev=[]
            common_port=names.id(('common',t))
            for i,row in enumerate(types):
                normal,first,second=row[:3]
                x=prod(2*i,t,base,prev);y=prod(2*i+1,t,base,prev)
                z=names.id(('wire',i,t));prev.append(z)
                emit([-normal,-x,z]);emit([-normal,-y,z]);emit([-normal,x,y,-z])
                for bit,flag in zip(loads,row[3:]):
                    if mask>>bit&1:emit([-flag,z])
                    else:emit([-flag,-x,z]);emit([-flag,x,-z])
                for k,flag in enumerate((first,second)):
                    if common:
                        emit([-flag,-common_port,x]);emit([-flag,common_port,-x])
                    if partners is not None:emit([-flag,x if partners>>k&1 else -x])
                    if mask>>(4+k)&1:
                        emit([-flag,-x,z]);emit([-flag,x,-z])
                    else:emit([-flag,-z])
            z=prod(2*len(types),t,base,prev)
            emit([z if want else -z])
        if certificate is not None:
            assert s.solve() is False
            certificate.with_suffix('.cnf').write_text(f'p cnf {names.top} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
            certificate.with_suffix('.drat').write_text('\n'.join(s.get_proof())+'\n')
            return False
        s.conf_budget(conflicts)
        return s.solve_limited()

def extend(rows,extra):
    pins=list((t,p) for t,p in rows if t.bit_count()==2)
    loads=[]
    for j,(tag,port) in enumerate(extra):
        pins.append((tag|(1<<(6+j)),port))
        loads.extend([6+j]*(2-tag.bit_count()))
    positive=sorted({a|b for (a,_),(b,_) in __import__('itertools').combinations(pins,2)})
    return tuple([(a,0,p) for a,p in sorted(pins)]+[(a,1,None) for a in positive]),tuple(loads)

if __name__=='__main__':
    base=Path(sys.argv[1])
    for idx,(common,rows) in enumerate(jobs(base)):
        if not common:continue
        extra=set((t,p) for t,p in rows if t.bit_count()<2)
        for single in sorted(extra):
            tests,loads=extend(rows,[single])
            result=check(common,tests,loads)
            print(idx,single,result,flush=True)
            if result is False:break
