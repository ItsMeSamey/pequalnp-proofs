"""Check a real CMR executable against independent finite references."""
from functools import partial
from random import Random
import sys
from check_line import direct
from check_first_space import check as check_first_space
from exact_line import exact_line
from graphic import is_graphic, is_graphic_cmr

if __name__ == "__main__":
    cmr = partial(is_graphic_cmr, executable=sys.argv[1])
    rng = Random(1189)
    fano = list(range(1, 8))
    dual_fano = [1, 2, 4, 8, 7, 11, 13]
    assert not cmr(fano) and not cmr(dual_fano)
    for _ in range(60):
        cols = [rng.randrange(32) for _ in range(rng.randrange(5, 11))]
        assert cmr(cols) == is_graphic(cols), cols
    for _ in range(60):
        cols = [rng.randrange(32) for _ in range(rng.randrange(3, 9))]
        pins = tuple(i for i in range(len(cols)) if rng.randrange(5) == 0)
        result = exact_line(cols, 1, 2, 4, forced=pins, graphic=cmr)
        assert (result is not None) == direct(cols, pins)
    for _ in range(30):
        n = rng.randrange(2, 8)
        check_first_space([rng.randrange(4) for _ in range(n)],
                          [rng.randrange(4) for _ in range(n)], graphic=cmr)
    # Both terminal recognition answers reached without a direct target column.
    assert exact_line([8,9], 1,2,4, graphic=cmr) == (0,1)
    assert exact_line([2,3], 1,2,4, graphic=cmr) is None
    print("2 excluded minors, 60 recognition comparisons, 62 exact-line controls and 30 first-space bases passed")
