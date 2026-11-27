"""Free conjunctions between paid ORs. Emit DIMACS, a scalar-verified control and DRAT candidate."""
import argparse,hashlib,itertools,json
from pathlib import Path
from pysat.formula import IDPool
P=argparse.ArgumentParser();P.add_argument('--run',action='store_true');P.add_argument('--out',type=Path,required=True);opt=P.parse_args()
out=opt.out;out.mkdir(parents=True,exist_ok=True)
# Flags in order center U, leaves a,b,c, center V, leaves d,e,f.
edge=[(1<<i)|(1<<j) for i,j in [(0,1),(0,2),(0,3),(4,5),(4,6),(4,7)]]
cases=[(x,False) for x in edge]+[(x|y,True) for x,y in itertools.combinations(edge,2)]
# Each OR's inputs are conjunctions of selected flags/prior ORs, and final output is a conjunction.
control=[([1],[5]),([2],[6]),([3],[7]),([8],[9]),([8,9],[10,11]),([12],[0,4])]
def scalar(raw):
    flags=sum(0 for _ in ())
    for j,e in enumerate(edge):
        if (raw>>j)&1:flags|=e
    w=[bool((flags>>k)&1) for k in range(8)]
    for left,right in control:w.append(all(w[i] for i in left) or all(w[i] for i in right))
    return w[-1]
assert all(scalar(x)==(x.bit_count()>=2) for x in range(64))
def encode(r):
    ids=IDPool();clauses=[]
    def term(slot,t,mask,prev):
        z=ids.id(('z',slot,t)); bads=[]
        for k in range(8+len(prev)):
            use=ids.id(('use',slot,k))
            if k<8:
                if not mask>>k&1:bads.append(use)
            else:
                v=prev[k-8];bad=ids.id(('bad',slot,t,k))
                clauses.extend([[-bad,use],[-bad,-v],[bad,-use,v]]);bads.append(bad)
        clauses.extend([[-z,-b] for b in bads]);clauses.append([z,*bads]);return z
    for t,(mask,truth) in enumerate(cases):
        prev=[]
        for i in range(r):
            a,b=(term(2*i+j,t,mask,prev) for j in (0,1))
            y=ids.id(('y',i,t));clauses.extend([[-a,y],[-b,y],[a,b,-y]]);prev.append(y)
        z=term(2*r,t,mask,prev);clauses.append([z if truth else -z])
    return ids,clauses
def check_control():
    ids,clauses=encode(6);terms=[p for pair in control for p in pair]+[[13]];A={}
    for t,(mask,truth) in enumerate(cases):
        vals=[bool(mask>>k&1) for k in range(8)]
        for i,sources in enumerate(terms):
            avail=8+min(i//2,6)
            for k in range(avail):
                A[ids.id(('use',i,k))]=k in sources
                if k>=8:A[ids.id(('bad',i,t,k))]=k in sources and not vals[k]
            val=all(vals[k] for k in sources);A[ids.id(('z',i,t))]=val
            if i%2:
                val=val or A[ids.id(('z',i-1,t))];vals.append(val);A[ids.id(('y',i//2,t))]=val
    assert all(any(A[abs(x)]==(x>0) for x in c) for c in clauses)
    print('control',len(cases),len(clauses),'clauses, 64 full tests',flush=True)
check_control()
ids,clauses=encode(5)
cnf=out/'pair.cnf';cnf.write_text(f'p cnf {ids.top} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
print('five OR',ids.top,len(clauses),hashlib.sha256(cnf.read_bytes()).hexdigest(),flush=True)
if opt.run:
    from pysat.solvers import Cadical195
    with Cadical195(bootstrap_with=clauses,with_proof=True) as solver:
        if solver.solve():
            chosen=set(solver.get_model());terms=[]
            for i in range(11):terms.append([k for k in range(8+i//2) if ids.id(('use',i,k)) in chosen])
            for raw in range(64):
                mask=0
                for j,e in enumerate(edge):
                    if raw>>j&1:mask|=e
                vals=[bool(mask>>k&1) for k in range(8)]
                for i in range(5):vals.append(any(all(vals[k] for k in terms[2*i+s]) for s in (0,1)))
                assert all(vals[k] for k in terms[-1])==(raw.bit_count()>=2)
            (out/'witness.json').write_text(json.dumps(terms));print('SAT 64/64',terms)
        else:
            (out/'pair.drat').write_text('\n'.join(solver.get_proof())+'\n');print('UNSAT; DRAT verification required')
