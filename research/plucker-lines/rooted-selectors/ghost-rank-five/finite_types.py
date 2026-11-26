"""Fixed-rank SAT via explicit hyperplane separators, with no XOR gates."""
from itertools import product, combinations_with_replacement
import sys
from pysat.solvers import Solver


def dot(a,b):
    return (a&b).bit_count()%2


def chart(rank,alpha,beta,delta,gamma):
    q=1<<(rank-1)
    t=6^q^(alpha<<3)
    named=[(1,0),(2,0),(4,0),(3^(beta<<3)^(gamma*q),0),(5^(delta<<3)^(gamma*q),1)]
    named += [(1<<a,0) for a in range(3,rank-1)]
    return q,t,named


def test(rank,params):
    q,t,named=chart(rank,*params)
    space=range(1<<rank)
    optional=[(v,w) for v in space for w in (0,1) if (v,w) not in named]
    ids={vw:j+1 for j,vw in enumerate(optional)}
    nvar=len(ids)
    clauses=[]
    choose=[[],[]]
    for d in space:
        if not dot(d,1) or dot(d,t):
            continue
        dq=dot(d,q)
        admissible=[(v,w) for v,w in optional if not dot(d,v)]
        mand=[(v,w) for v,w in named if not dot(d,v)]
        certificates=[]
        nvar+=1
        marginal=nvar
        choose[dq].append(marginal)
        # f and f+d agree on the d-zero columns.
        for f in space:
            if f>(f^d):
                continue
            if dot(f,t) and all(not dot(f,v) for v,w in mand):
                hit=[ids[v,w] for v,w in admissible if dot(f,v)]
                clauses.append([-marginal,*hit])
                nvar+=1
                certificates.append(nvar)
                clauses.extend([[-nvar,-p] for p in hit])
            if dot(f,t)==dq and all(dot(f,v)==w for v,w in mand):
                nvar+=1
                certificates.append(nvar)
                clauses.extend([[-nvar,-ids[v,w]] for v,w in admissible if dot(f,v)!=w])
        clauses.append(certificates)
    clauses.extend(choose)
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        if solver.solve():
            vals=set(solver.get_model())
            return named+[vw for vw,p in ids.items() if p in vals]
    return None


if __name__=='__main__':
    rank=int(sys.argv[1]) if len(sys.argv)>1 else 5
    dim=1<<(rank-4)
    def parameters():
        if "--orbits" not in sys.argv:
            yield from product(range(dim),range(dim),range(dim),range(2))
            return
        # The contracted ground elements can be permuted.
        for types in combinations_with_replacement(range(8),rank-4):
            vectors = [sum(((kind>>a)&1)<<i for i,kind in enumerate(types)) for a in range(3)]
            for gamma in (0,1):
                yield (*vectors,gamma)
    for j,params in enumerate(parameters()):
        answer=test(rank,params)
        if answer is not None:
            print("counterexample",params,answer,flush=True)
            break
        if j%16==15:
            print("checked",j+1,flush=True)
    else:
        print("all charts UNSAT at rank",rank)
