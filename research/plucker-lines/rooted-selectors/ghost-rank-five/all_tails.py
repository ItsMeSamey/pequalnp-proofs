"""Check every ordinary contraction tail in four incremental SAT queries."""
import sys
from pysat.solvers import Solver


def members(mask):
    while mask:
        bit=mask & -mask
        yield bit.bit_length()  # Variable ID is 1 + the zero-based typed vector index.
        mask ^= bit


def check(rank, induct=False):
    n=1<<rank
    q=n>>1
    positive=sum(1<<(2*v+1) for v in range(n))
    full=(1<<(2*n))-1
    evals=[sum(3<<(2*v) for v in range(n) if (v&f).bit_count()%2) for f in range(n)]
    mandatory=sum(1<<(2*v) for v in [1,4,*[1<<i for i in range(3,rank-1)]])
    nvar=2*n
    clauses=[[p] for p in members(mandatory)]
    # The distinguished root t has zero label. An ordinary copy of t would
    # immediately let the dual weight vary at fixed primal support.
    clauses += [[-(2*2+1)],[-(2*2+2)]]
    splits=[]
    if induct:
        for h in range(rank-3):
            nvar+=1
            first=((1<<h)-1)<<3
            splits.append((nvar,first,(q-8)^first))
    marginal=[[],[]]
    # Anchored d has its s bit one and its t bit zero.
    for d in range(1,n,4):
        permitted=full ^ evals[d]
        dq=int(bool(d&q))
        nvar+=1
        choose=nvar
        marginal[dq].append(choose)
        certificates=[]
        inactive=[]
        for f in range(n):
            if f>(f^d):
                continue
            ft=int(bool(f&2))
            barred=permitted & evals[f]
            if ft and not barred&mandatory:
                hits=list(members(barred))
                clauses.append([-choose,*hits])
                nvar+=1
                certificates.append(nvar)
                inactive.append(nvar)
                clauses.extend([[-nvar,-p] for p in hits])
            barred=permitted & (positive ^ evals[f])
            if ft==dq and not barred&mandatory:
                nvar+=1
                certificates.append(nvar)
                clauses.extend([[-nvar,-p] for p in members(barred)])
        clauses.append(certificates)
        for selector,first,last in splits:
            required=last if dq else first
            if required & ~d:
                clauses.append([-selector,*inactive])
                clauses.append([-selector,-choose])
    clauses.extend(marginal)
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        for gamma in (0,1):
            for eps in (0,1):
                nvar+=1
                mode=nvar
                # k=i+t+q+tail; j=s+i+gamma*q+tail;
                # l=s+i+t+(1+gamma)*q+tail. An arbitrary tail is a multiple
                # of eight less than q. Its weight is zero in the chosen gauge.
                for base,w in ((6^q,0),(5^(gamma*q),eps),(7^((1-gamma)*q),1-eps)):
                    solver.add_clause([-mode,*[2*(base^a)+w+1 for a in range(0,q,8)]])
                for part in [([a] if a else []) for a in ([item[0] for item in splits] or [None])]:
                    if not solver.solve(assumptions=[mode,*part]):
                        continue
                    model=set(solver.get_model())
                    types=[(v,w) for v in range(n) for w in (0,1) if 2*v+w+1 in model]
                    print("SAT",rank,gamma,eps,types,flush=True)
                    return False
                print("UNSAT",rank,gamma,eps,flush=True)
    return True


if __name__=='__main__':
    check(int(sys.argv[1]) if len(sys.argv)>1 else 5, "--induct" in sys.argv)
