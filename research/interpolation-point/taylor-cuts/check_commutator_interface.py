from unittest.mock import patch
from barrington_cnf_rail import IDENT
from commutator_source_proof import prove_interface,verify_interface,compile_verified


def main():
    # (z OR x) AND (z OR NOT x) forces z; the other child forces NOT z.
    k=[(1,2),(1,-2)]
    g=[(-1,3),(-1,-3)]
    f=k+g
    cert=prove_interface(3,f)
    assert cert[0]=="interface-unsat" and [side for side,_ in cert[1]]==[0,1]
    assert all(any(all(any(bool(m&(1<<(abs(x)-1)))==(x>0) for x in c) for c in child)
                   for m in range(8)) for child in (k,g))
    assert verify_interface(3,f,(),cert)
    with patch("commutator_source_proof._compile",side_effect=AssertionError("expanded")):
        assert compile_verified(3,f,{():cert})==([],IDENT)
    for bad in [(cert[0],cert[1][:-1]),(cert[0],cert[1][::-1]),
                (cert[0],((1,cert[1][0][1]),cert[1][1]))]:
        assert not verify_interface(3,f,(),bad)
    assert not verify_interface(3,f,(0,),cert)
    sat=k+[(1,3),(1,-3)]
    witness=prove_interface(3,sat)
    assert witness[0]=="sat" and verify_interface(3,sat,(),witness)
    assert not verify_interface(3,sat,(),("sat",0))
    for rows,kind in [([(1,),(-1,),(2,),(2,)],"interface-unsat"), ([(1,),(2,)],"sat")]:
        answer=prove_interface(2,rows)
        assert answer[0]==kind and verify_interface(2,rows,(),answer)
        if kind=="interface-unsat":
            assert len(answer[1])==1
    print("two satisfiable children force opposite shared bits; witness merging, empty interfaces and tampering passed")


if __name__=="__main__":
    main()
