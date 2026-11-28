from check_raw_lookahead_04 import main as small
from cofactor_mux_fixture import main as mux_words, mux_array
from raw_lookahead import solve

if __name__ == "__main__":
    small()
    mux_words()
    for m in (3, 4):
        for no in (False, True):
            inputs, gates, out = mux_array(m, no)
            status, baseline, pilot, scores, raw = solve(inputs, gates, output=out)
            assert baseline == 2*m + (3 if no else -1)
            assert pilot == 0 and scores == (0, 0)
            assert status == ("unsat" if no else "sat")
    print("all four exact mux baselines, selected pilots and cofactor verdicts verified")
