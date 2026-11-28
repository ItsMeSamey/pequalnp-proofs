"""Bounded independent majority-operation, CSP and physical controls for 04."""
from itertools import product
from majority_row_csp import majority_assignment, solve


def op_tables(d):
    forced={}
    unknown=[]
    for triple in product(d,repeat=3):
        repeated=[x for x in d if triple.count(x)>=2]
        if repeated:
            forced[triple]=repeated[0]
        else:
            unknown.append(triple)
    for outputs in product(d,repeat=len(unknown)):
        yield forced | dict(zip(unknown,outputs))


def exhaustive_relation(left,right,rel):
    # Exhaust every candidate majority on the left; exhaust viable right-hand
    # outputs independently at every ordered triple (no right/right constraints).
    triples=[tuple(zip(*rows)) for rows in product(rel,repeat=3)]
    for first in op_tables(left):
        available={t:{b for b in right if t.count(b)>=2} or set(right)
                   for t in product(right,repeat=3)}
        for x,y in triples:
            available[y].intersection_update(b for b in right if (first[x],b) in rel)
            if not available[y]:
                break
        else:
            return True
    return False


def check(dom,edges,expected):
    adj=[{} for d in dom]
    for i,j,rel in edges:
        adj[i][j]=rel
        adj[j][i]={(b,a) for a,b in rel}
    status,ops,chosen=majority_assignment(dom,adj,max_pc_vars=None)
    assert status==expected
    if ops is not None:
        for d,op in zip(dom,ops):
            for a,b in product(d,repeat=2):
                assert op[a,b,a]==op[b,a,a]==op[a,a,b]==a
        for i,j,rel in edges:
            for rows in product(rel,repeat=3):
                l,r=zip(*rows)
                assert (ops[i][l],ops[j][r]) in rel
    if status=="sat":
        assert all((chosen[i],chosen[j]) in rel for i,j,rel in edges)
    if status in ("sat","unsat"):
        assert (status=="sat")==any(all((v[i],v[j]) in rel for i,j,rel in edges)
                                    for v in product(*dom))


def main():
    d=(1,4,9)
    binary=(0,2)
    # All 64 relations between a binary and a ternary sort.
    pairs=list(product(binary,d))
    for mask in range(1<<len(pairs)):
        rel={p for i,p in enumerate(pairs) if mask>>i&1}
        expected="unsat" if not rel else ("sat" if exhaustive_relation(binary,d,rel) else "skip")
        check([binary,d],[(0,1,rel)],expected)
    neq={(a,b) for a in d for b in d if a!=b}
    assert not exhaustive_relation(d,d,neq)
    check([d,d],[(0,1,neq)],"skip")
    bij={(1,4),(4,9),(9,1)}
    assert exhaustive_relation(d,d,bij)
    check([d,d],[(0,1,bij)],"sat")
    distinct={(0,2),(2,0)}
    check([binary]*3,[(0,1,distinct),(1,2,distinct),(0,2,distinct)],"unsat")
    check([],[],"sat")
    clauses=[(1,3),(2,4),(6,5)]
    status,stats,raw=solve(5,[(0,1)],clauses=clauses,max_pc_vars=0)
    assert status=="skip" and stats["reason"]=="cap" and raw is None
    state,stats,raw=solve(5,[(0,1)],clauses=clauses,max_pc_vars=None)
    assert state=="sat" and len(raw)==5
    w=list(raw)+[1-(raw[0]&raw[1])]
    assert all(any(w[abs(l)-1]==(l>0) for l in row) for row in clauses)
    state,stats,raw=solve(2,[(0,1)],pins=[(0,0),(2,0)])
    assert state=="unsat" and raw is None
    print("64 exhaustive binary/ternary relations, ternary nonchart/transport, odd cycle, empty CSP, raw skip/SAT/UNSAT")


if __name__=="__main__":
    main()
