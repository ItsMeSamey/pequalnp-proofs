from itertools import product
from unittest.mock import patch
from barrington_cnf_rail import compile_cnf,evaluate,IDENT,RHO
from commutator_source_proof import compile_verified,propose,simplify


def main():
    h=[(-1,-2)]*4
    g=list(product((3,-3),(4,-4)))
    j=list(product((5,-5),(6,-6)))*2
    source=h+g+j
    core=propose(6,g)[()]
    local={(0,1):core}  # Source is ((H AND G) AND J).
    assert simplify(6,source,local) is False
    with patch("commutator_source_proof._compile",side_effect=AssertionError("expanded")):
        assert compile_verified(6,source,local)==([],IDENT)
        assert compile_verified(6,source,propose(6,source))==([],IDENT)
    assert len(compile_cnf(6,source)[0])==1024
    for wrong in [{(0,0):core},{(0,1):(core[0],(core[1][0],(),core[1][2]))}]:
        try:
            simplify(6,source,wrong)
        except ValueError:
            continue
        raise AssertionError("tampered proof accepted")
    sat=h+g[:3]+j[:3]
    for formula in [sat,[],[()],[(1,-1),(1,2)],[(1,2),(1,2)],[(2,),(-2,)]]:
        gates,tail=compile_verified(6,formula,propose(6,formula))
        for mask in range(64):
            val=all(any(bool(mask&(1<<(abs(x)-1)))==(x>0) for x in c) for c in formula)
            assert evaluate(gates,tail,mask)==(RHO if val else IDENT)
    print("lower's 1024-gate source collapsed pre-expansion; local tampering rejected and 384 assignment checks passed")


if __name__=='__main__':
    main()
