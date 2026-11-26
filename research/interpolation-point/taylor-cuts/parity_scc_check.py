"""Exhaustive matching and free-bit oracle for the multi-XOR peeling solver."""
from itertools import product
from random import Random
from functools import reduce
from operator import xor
from choice_cover_one_xor import Option
from parity_scc_peel import peel


def main():
    rng=Random(18105)
    cases=0
    for _ in range(140):
        n=rng.randrange(1,6)
        labels=rng.randrange(1,5)
        base=[Option(i,i, rng.randrange(1<<labels)) for i in range(n)]
        options=[[b]+[Option(rng.randrange(n),100*i+j,rng.randrange(1<<labels))
                      for j in range(rng.randrange(4))] for i,b in enumerate(base)]
        free=[rng.randrange(1<<labels) for _ in range(rng.randrange(3))]
        reachable={reduce(xor,(v.parity for v in match),0)^reduce(xor,(x for j,x in enumerate(free) if f>>j&1),0)
                   for match in product(*options) if len({v.resource for v in match})==n
                   for f in range(1<<len(free))}
        for t in range(1<<labels):
            status,selected,f,stalled=peel(options,base,t,free)
            if status=='UNSAT':
                assert t not in reachable
            elif status=='SAT':
                assert t in reachable and len({v.resource for v in selected})==n
                assert all(o in row for o,row in zip(selected,options))
                assert t==reduce(xor,(v.parity for v in selected),0)^reduce(xor,(v for j,v in enumerate(free) if f>>j&1),0)
            else:
                assert stalled
            es,em,ef,_=peel(options,base,t,free,exact=True)
            assert (es=='SAT')==(t in reachable) and es!='UNKNOWN'
            if em is not None:
                assert len({v.resource for v in em})==n
                assert all(v in row for v,row in zip(em,options))
                assert t==reduce(xor,(v.parity for v in em),0)^reduce(xor,(v for j,v in enumerate(free) if ef>>j&1),0)
            cases+=1
    row=[Option(0,i,i) for i in (0,1,2)]
    assert peel([row],[row[0]],3)[0]=='UNKNOWN'
    assert peel([row],[row[0]],1)[0]=='UNKNOWN'
    # A later singleton contributes direction 1, unlocking the rank-two SCC.
    assert peel([row],[row[0]],3,exact=True)[0]=='UNSAT'
    assert peel([row],[row[0]],1,exact=True)[0]=='SAT'
    # Each exceptional matching has hidden gain 4 that must be repaired
    # by a disjoint peeled cycle or a free column of that label.
    special=[Option(0,0,0),Option(0,1,5),Option(0,2,2)]
    helper=[Option(1,3,0),Option(1,4,4)]
    for target in (1,5,2,6):
        status,chosen,f,_=peel([special,helper],[special[0],helper[0]],target,exact=True)
        assert status=='SAT' and reduce(xor,(o.parity for o in chosen),0)==target
        status,chosen,f,_=peel([special],[special[0]],target,[4],exact=True)
        assert status=='SAT' and (chosen[0].parity^(4 if f else 0))==target
    b=Option(1,3,0)
    for target in range(4):
        assert peel([row,[b,Option(1,4,1)]],[row[0],b],target)[0]=='SAT'
    print(f'{cases} exhaustive target comparisons; stalled and cascading examples passed.')


if __name__=='__main__':
    main()
