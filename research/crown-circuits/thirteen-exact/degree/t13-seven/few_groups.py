"""Pure indicators and constrained mixed raw injections for small pure-group cases."""
from itertools import combinations,permutations
from collections import Counter
from pathlib import Path
import sys
from pysat.formula import IDPool
from pysat.solvers import Cadical195
from pysat.card import CardEnc
def check(p,tags,budget,private=False,final=False,certificate=None,starcuts=False,ordinary_position=None):
    raw_tags=[]
    inputs=[]
    loads=[]
    for tag in tags:
        if tag.bit_count()<2:
            raw_tags.append(tag)
            bit=p+len(loads)
            loads.append(2-tag.bit_count());tag|=1<<bit
        inputs.append(tag)
    cases=[(x,False) for x in set(inputs)]+[(x,True) for x in {x|y for x,y in combinations(inputs,2)}]
    available=p-int(private); ordinary=p-2-int(private or final)
    n=ordinary+sum(loads);pool=IDPool()
    with Cadical195(with_proof=certificate is not None) as s:
        clauses=[]
        def emit(cl):
            if certificate is not None:clauses.append(cl)
            s.add_clause(cl)
        kinds=[[pool.id(('kind',j,k)) for k in range(len(loads)+1)] for j in range(n)]
        for row in kinds:
            emit(row)
            for a,b in combinations(row,2):emit([-a,-b])
        for j,k in enumerate([ordinary,*loads]):
            for cl in CardEnc.equals([r[j] for r in kinds],k,vpool=pool).clauses:emit(cl)
        for j in range(len(loads)):
            earlier=[k for k in range(j) if raw_tags[k]==raw_tags[j]]
            if not earlier:continue
            k=earlier[-1]
            for pos,row in enumerate(kinds):
                emit([-row[j+1],*[r[k+1] for r in kinds[:pos]]])
        def product(t,slot,mask,prev):
            bad=[pool.id(('false',slot))]
            for j in range(available+len(prev)):
                use=pool.id(('use',slot,j))
                if j<available:
                    if not mask>>j&1:bad.append(use)
                else:
                    w=prev[j-available];z=pool.id(('bad',t,slot,j))
                    emit([-z,use]);emit([-z,-w]);emit([z,-use,w]);bad.append(z)
            v=pool.id(('prod',t,slot))
            for b in bad:emit([-v,-b])
            emit([v,*bad]);return v
        for t,(mask,want) in enumerate(cases):
            prev=[]
            for i,row in enumerate(kinds):
                a=product(t,2*i,mask,prev);b=product(t,2*i+1,mask,prev)
                z=pool.id(('wire',t,i));prev.append(z);flag=row[0]
                emit([-flag,-a,z]);emit([-flag,-b,z]);emit([-flag,a,b,-z])
                for j,flag in enumerate(row[1:]):
                    if mask>>(p+j)&1:emit([-flag,z])
                    else:emit([-flag,-a,z]);emit([-flag,a,-z])
            z=product(t,2*n,mask,prev)
            if final or (private and mask>>(p-1)&1):
                v=product(t,2*n+1,mask,prev)
                if want:emit([z,v])
                else:emit([-z]);emit([-v])
            else:emit([z if want else -z])
        if starcuts:
            from local_schedule import solve,trace
            assert ordinary==1 and not private and not final
            tests={m:t for t,(m,w) in enumerate(cases)}
            for axis in range(p):
                local=[i for i,t in enumerate(tags) if t>>axis&1]
                if len(local)!=3:continue
                local.sort(key=lambda i:(tags[i].bit_count()!=2,i))
                d=sum(tags[i].bit_count()==2 for i in local)
                marks=[(inputs[i]>>p).bit_length() for i in local[d:]]
                for gate,row in enumerate(kinds):
                    options=[]
                    for before in range(4-d):
                        labels=trace(before,d,pre=starcuts=="pre") if starcuts in ("full","pre") else [(pair,()) for _,pair in solve(before,d)]
                        for pair,marked in labels:
                            for left,right in set(permutations(pair)):
                                flag=pool.id(('signature',axis,gate,before,left,right,marked));options.append(flag)
                                for k,mark in enumerate(marks):
                                    if k<before:emit([-flag,*[old[mark] for old in kinds[:gate]]])
                                    else:
                                        for old in kinds[:gate]:emit([-flag,-old[mark]])
                                for test in range(1,7):
                                    m=0
                                    for j,i in enumerate(local):
                                        if test>>j&1:m|=inputs[i]
                                    t=tests[m]
                                    for pos,w in enumerate([left,right]):
                                        z=pool.id(('prod',t,2*gate+pos))
                                        emit([-flag,z if w>>(test-1)&1 else -z])
                                    for local_mark,wt in zip(marks,marked):
                                        y=pool.id(('marked-value',local_mark,t))
                                        emit([-flag,y if wt>>(test-1)&1 else -y])

                    emit([-row[0],*options])
            if starcuts in ("full","pre"):
                for t in range(len(cases)):
                    for j in range(1,1+len(loads)):
                        if loads[j-1]!=1:continue
                        y=pool.id(('marked-value',j,t))
                        for i,row in enumerate(kinds):
                            z=pool.id(('prod',t,2*i)) if starcuts=='pre' else pool.id(('wire',t,i))
                            emit([-row[j],y,-z]);emit([-row[j],-y,z])

        if ordinary_position is not None:
            # Three identical triples, one ordinary OR after 2 or 3 labels per group.
            assert p==3 and tuple(tags)==(1,1,1,2,2,2,4,4,4) and starcuts
            pos=ordinary_position
            emit([kinds[pos][0]])
            complete=pos-6
            for g in range(3):
                last=3*(g+1)
                if g<complete:emit([r[last] for r in kinds[:pos]])
                else:
                    for r in kinds[:pos]:emit([-r[last]])
                if g and (g-1<complete)==(g<complete):
                    for j,r in enumerate(kinds):
                        emit([-r[3*g+1],*[old[3*(g-1)+1] for old in kinds[:j]]])
            a=pool.id(('prod',tests[inputs[0]|inputs[2]],2*pos))
            b=pool.id(('prod',tests[inputs[1]|inputs[2]],2*pos))
            emit([a]);emit([-b])
        if certificate is not None:
            assert s.solve() is False
            certificate.with_suffix('.cnf').write_text(f'p cnf {pool.top} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
            certificate.with_suffix('.drat').write_text('\n'.join(s.get_proof())+'\n')
            return False
        s.conf_budget(budget);return s.solve_limited()
if __name__=='__main__':
    base=Path(sys.argv[1]);p=int(sys.argv[2])
    models={}
    for l in (base/'qmodels.in').read_text().splitlines():
        q,g,c,b,quart,dirty=map(int,l.split())
        if q!=p:continue
        edges=[1<<i|1<<j for i in range(p) for j in range(i) if g>>(i*(i-1)//2+j)&1]
        mixed=sum(([1<<i]*(3+(quart>>i&1)-sum(x>>i&1 for x in edges)) for i in range(p)),[])
        mixed += [0]*(13-len(mixed)-len(edges))
        models[g,quart]=edges,mixed
    memo={}
    for (g,q),(edges,mixed) in sorted(models.items()):
        done=False
        for num in range(1,5):
            for extra in sorted(set(combinations(mixed,num)),key=lambda s:s.count(0)):
                inputs=tuple(sorted(edges+list(extra)))
                if len(inputs)<3:continue
                if inputs not in memo:memo[inputs]=check(p,inputs,1000)
                if memo[inputs] is False:
                    print(g,q,inputs,'UNSAT',flush=True);done=True;break
            if done:break
        if not done:print(g,q,'open',len(memo),flush=True)
