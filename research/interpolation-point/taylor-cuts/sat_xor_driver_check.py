"""Parent-level status, process cleanup, and witness validation fixtures."""
import multiprocessing
import time
from unittest.mock import patch
import sat_xor_driver as driver


def main():
    before={p.pid for p in multiprocessing.active_children()}
    with patch.object(driver,"_run",side_effect=lambda *args:time.sleep(5)):
        timed=driver.solve_sat_xor(1,[],budgets={"brute":.03},stages=("brute",))
    assert timed["status"]=="UNKNOWN" and timed["reports"][0]["status"]=="TIMEOUT"
    assert {p.pid for p in multiprocessing.active_children()}==before
    with patch.object(driver,"_run",return_value=("SAT",0,{},())):
        bad=driver.solve_sat_xor(1,[(1,)],stages=("brute",))
    assert bad["status"]=="UNKNOWN" and bad["reports"][0]["status"]=="ERROR"
    with patch.object(driver,"_run",side_effect=RuntimeError("simulated backend failure")):
        bad=driver.solve_sat_xor(0,[],stages=("brute",))
    assert bad["status"]=="UNKNOWN" and bad["reports"][0]["status"]=="ERROR"
    result=driver.solve_sat_xor(2,[(1,),(-1,-2)],[(2,1)],stages=("anf","brute"))
    assert result["status"]=="UNSAT"
    skip=driver.solve_sat_xor(1,[(1,)],stages=("brute",),budgets={"brute":0})
    assert skip["status"]=="UNKNOWN"
    good=driver.solve_sat_xor(2,[(-1,2),(1,-2)],[(1,1)],stages=("brute",))
    assert good["status"]=="SAT" and good["witness"]==3
    try:
        driver.solve_sat_xor(1,[],[(1,1.0)])
    except ValueError:
        pass
    else:
        raise AssertionError("floating-point XOR RHS accepted")
    print("deadline/cleanup, wrong witness, backend error, derived rows, disabled fallback, SAT witness, RHS validation")


if __name__=="__main__":
    main()
