"""Two private products are clean terminals. Reserve their two collector ORs."""
from mixed_partner_budget import extend
from pathlib import Path
import sys
from itertools import permutations
from pysat.formula import IDPool
from pysat.solvers import Cadical195
def solve(tests,loads,certificate=None):
    pool=IDPool()
    with Cadical195(with_proof=certificate is not None) as s:
        clauses=[]
        def emit(clause):
            if certificate is not None:clauses.append(clause)
            s.add_clause(clause)
        def term(slot,t,x,prev):
            bad=[pool.id(('falseInput',slot))]
            for j in range(4+len(prev)):
                use=pool.id(('use',slot,j))
                if j<4:
                    if not x&(1<<j):bad.append(use)
                else:
                    v=prev[j-4];b=pool.id(('bad',slot,j,t))
                    emit([-b,use]);emit([-b,-v]);emit([b,-use,v]);bad.append(b)
            y=pool.id(('term',slot,t))
            for b in bad:emit([-y,-b])
            emit([y,*bad]);return y
        # Place two ordinary ORs among the marked raw injections.
        from itertools import combinations
        data=[]
        seq=[-1,-1,*loads]
        schedules=sorted(set(permutations(seq)))
        flags=[pool.id(('flag',i)) for i in range(len(schedules))]
        emit(flags)
        for t,(mask,target,partner) in enumerate(tests):
            prev=[]
            for i in range(len(seq)):
                a=term(2*i,t,mask,prev);b=term(2*i+1,t,mask,prev);z=pool.id(('wire',i,t));prev.append(z)
                for row,flag in zip(schedules,flags):
                    k=row[i]
                    if k==-1:
                        emit([-flag,-a,z]);emit([-flag,-b,z]);emit([-flag,a,b,-z])
                    elif mask>>k&1:emit([-flag,z])
                    else:emit([-flag,-a,z]);emit([-flag,a,-z])
            ports=[term(2*len(seq)+j,t,mask,prev) for j in range(3)]
            active=[ports[2]]+[ports[j] for j in range(2) if mask>>(4+j)&1]
            if target:emit(active)
            else:
                for a in active:emit([-a])
                for j in range(2):emit([ports[j] if partner>>j&1 else -ports[j]])
        if certificate is not None:
            assert not s.solve()
            certificate.with_suffix('.cnf').write_text(f'p cnf {pool.top} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
            certificate.with_suffix('.drat').write_text('\n'.join(s.get_proof())+'\n')
            return False
        s.conf_budget(2500);return s.solve_limited()

if __name__=='__main__':
    base=Path(sys.argv[1]);memo={};profiles=set()
    for l in (base/'p6-200.live').read_text().splitlines():
        _,a,b,*tags=map(int,l.split())
        profiles.add(tuple(sorted((u,(a>>i&1)|((b>>i&1)<<1)) for i,u in enumerate(tags))))
    if len(sys.argv)>3:
        import json
        ledger=open(sys.argv[3],'w')
    for i,r in enumerate(sorted(profiles)):
        extras=sorted(set(x for x in r if x[0].bit_count()<2),key=lambda x:(-x[0].bit_count(),x))
        subsets=[(x,) for x in extras]
        if len(sys.argv)>2:
            from itertools import combinations
            extra=[x for x in r if x[0].bit_count()==1]
            subsets+=sorted(set(combinations(extra,2)))
        for ext in subsets:
            q=extend(r,ext)
            if q not in memo:memo[q]=solve(*q)
            if memo[q] is False:break
        if len(sys.argv)>3 and memo[q] is False:print(json.dumps([r,ext]),file=ledger,flush=True)
        print(i,memo[q],len(memo),flush=True)
