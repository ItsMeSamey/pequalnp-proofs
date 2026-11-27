"""Focused integration regression for the bounded closure-cover stage."""
from time import sleep
from unittest.mock import patch
from sat_xor_driver import solve_sat_xor


def run(n,clauses,rows=(),seconds=1):
    return solve_sat_xor(n,clauses,rows,stages=("closure_cover",),budgets={"closure_cover":seconds})


def main():
    n=16
    star=[(-1,-i) for i in range(2,n+1)]
    sat=run(n,star,[(1<<j,int(j!=0)) for j in range(n)])
    assert sat["status"]=="SAT" and sat["witness"]==(1<<n)-2
    assert sat["reports"][0]["metrics"]["cover_size"]==1
    assert run(n,star,[(1,1),(2,1)])["status"]=="UNSAT"
    wide=run(3,[(1,2,3)])
    assert wide["status"]=="UNKNOWN" and wide["reports"][0]["status"]=="SKIP"
    with patch("two_sat_closure_cover.solve",return_value=(0,{})):
        invalid=run(1,[(1,)])
    assert invalid["status"]=="UNKNOWN" and invalid["reports"][0]["status"]=="ERROR"
    with patch("two_sat_closure_cover.solve",side_effect=lambda *args:sleep(5)):
        timeout=run(2,[],seconds=.03)
    assert timeout["status"]=="UNKNOWN" and timeout["reports"][0]["status"]=="TIMEOUT"
    print("closure_cover: SAT, UNSAT, width skip, rejected witness, timeout")


if __name__=="__main__":
    main()
