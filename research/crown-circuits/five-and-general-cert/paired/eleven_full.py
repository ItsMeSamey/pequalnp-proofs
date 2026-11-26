from pathlib import Path
from itertools import combinations
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
import sys
def test(h,bb,budget=15,name="cadical195",cert=None):
    full=65535;C=full^h;base=set(bb)|{full};cl={0}
    for b in bb:cl|={x|b for x in cl}
    cl.discard(0);paid={x:i+1 for i,x in enumerate(sorted(cl-base))};nxt=len(paid);rules=[]
    c=CardEnc.atmost(list(paid.values()),budget,top_id=nxt,encoding=EncType.seqcounter)
    nxt=max(nxt,c.nv);rules.extend(c.clauses)
    for v,z in paid.items():
        opts=[]
        for a,b in combinations(sorted(k for k in cl if k!=v and k&~v==0),2):
            if a|b!=v:continue
            nxt+=1;opts.append(nxt)
            for p in [a,b]:
                if p in paid:rules.append([-nxt,paid[p]])
        rules.append([-z]+opts)
    for j in range(0,8,2):
        if (v:=bb[j]|bb[j+1]) in paid:rules.append([paid[v]])
    selected={}
    for i in range(16):
        if not(C>>i&1):continue
        opts=[]
        for m in cl:
            if m&C==C^(1<<i):
                nxt+=1;selected[m]=nxt;opts.append(nxt)
                if m in paid:rules.append([-nxt,paid[m]])
        rules.append(opts)
    for a,b in combinations(selected,2):
        if (a&C)!=(b&C) and a|b!=full:rules.append([-selected[a],-selected[b]])
    with Solver(name=name,bootstrap_with=rules,with_proof=cert is not None) as s:
        s.conf_budget(300000);r=s.solve_limited()
        if cert is not None and r is False:
            (cert/'case.drat').write_text('\n'.join(s.get_proof())+'\n')
            with (cert/'case.cnf').open('w') as stream:
                print('p cnf',nxt,len(rules),file=stream)
                for clause in rules:print(*clause,0,file=stream)
        return r,s.accum_stats()['conflicts']
if __name__=='__main__':
 for ix,row in enumerate(open(sys.argv[1])):
     p=row.split()
     if p and p[0]=='witness':
         h,*b=map(int,p[1:]);r,c=test(h,b);print(ix,h,r,c,flush=True)
