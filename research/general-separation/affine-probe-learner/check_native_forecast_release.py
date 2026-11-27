"""Integrated replay for the five native forecast release entrypoints."""
from pathlib import Path
import runpy
from unittest.mock import patch

import primitive_forecast_extractor as diagnostic
import primitive_rewrite_chain as native
import state_dependent_interval_repair as intervals
import threshold_interval_solver as threshold


ENTRIES = (
    'check_primitive_rewrite_chain.py',
    'check_primitive_forecast_extractor.py',
    'check_verify_primitive_forecast_result.py',
    'check_state_dependent_interval_repair.py',
    'check_state_fork_median.py',
)


def rejects(error, fn, *args):
    try:
        fn(*args)
    except error:
        return
    raise AssertionError(f'{fn.__name__} accepted an invalid input')


def never(*args):
    raise AssertionError('backend invoked before source validation')


def shapes():
    n = 1
    cap = native.public_cap(n,1)
    predict = threshold.forecast_factory(n,((),0))
    sentinel = ((),-1)
    bad_gates = ({},'',{(-1,-1):None},[{}],[{-1:0,0:0}],[''],[()],[(0,)],[(0,0,0)])
    bad_sources = [ {},'',(),(-1,0),{():None,-1:None} ]
    bad_sources.extend((gates,-1) for gates in bad_gates)
    for source in bad_sources:
        rejects(ValueError,threshold.forecast_factory,n,source)
        rejects(ValueError,threshold.solve,n,source)
        rejects(ValueError,intervals.solve,n,source,cap,n,never)
        rejects(ValueError,diagnostic.extract,n,source,cap,n,never)
        rejects(threshold.UnsupportedQuery,predict,n,cap,(),source)
        rejects(threshold.UnsupportedQuery,predict,n,cap,((source,0),),sentinel)
    for gates in bad_gates:
        rejects(ValueError,native.endpoint,n,gates,-1,-1)
        rejects(ValueError,native.evaluate,n,gates,-1,0)
        rejects(ValueError,native.build_chain,n,gates,-1,0)
    for empty in ([],()):
        for source in ([empty,0],(empty,0)):
            assert native.evaluate(n,empty,0,1) == 1
            local = threshold.forecast_factory(n,source)
            assert local(n,cap,(),[empty,-1]) == 0
            assert threshold.solve(n,source)['assignment'] == 1
    assert native.evaluate(n,((0,0),),1,0) == 1
    assert native.evaluate(n,[[0,0]],1,1) == 0


def backends():
    cap = native.public_cap(1,0)
    source = ((),0)
    local = threshold.forecast_factory(1,source)
    # Valid NAND syntax computing a foreign source is outside the recognized
    # prefix language. The empty counterfactual history cannot mask that error.
    foreign = ((),-2)
    impossible = ((((),-1),1),)
    rejects(threshold.UnsupportedQuery,local,1,cap,impossible,foreign)
    for nonbit in (None,2,'1',{},(1,)):
        def invalid(*unused):
            return nonbit
        rejects(ValueError,intervals.solve,1,source,cap,1,invalid)
        rejects(ValueError,diagnostic.extract,1,source,cap,1,invalid)
        with patch.object(threshold,'forecast_factory',return_value=invalid):
            rejects(ValueError,threshold.solve,1,source)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('release checks require assertions enabled')
    base = Path(__file__).resolve().parent
    for entry in ENTRIES:
        runpy.run_path(str(base/entry),run_name='__main__')
    shapes()
    backends()
    print('Five frozen native forecast replays and parser controls passed.')
