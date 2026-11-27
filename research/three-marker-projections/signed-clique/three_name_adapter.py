"""Recover original column positions for an exact line in three named bits."""
from functools import partial
import os
from pathlib import Path
from shutil import which
import sys

_BACKEND = Path(__file__).resolve().parents[1] / "three-name-backend"
sys.path.insert(0, str(_BACKEND))
try:
    from exact_line import exact_line, pivots
    from graphic import is_graphic_cmr
finally:
    sys.path.pop(0)


def three_name(private, named, target):
    """Accept aligned integer column masks and a nonzero three-bit target."""
    private, named = tuple(private), tuple(named)
    if (len(private) != len(named) or type(target) is not int or not 1 <= target <= 7
            or any(type(p) is not int or p < 0 for p in private)
            or any(type(g) is not int or not 0 <= g <= 7 for g in named)):
        raise ValueError("expected aligned binary columns and a nonzero three-bit target")
    basis = [target]
    for unit in (1, 2, 4):
        if len(pivots([*basis, unit])) > len(basis):
            basis.append(unit)
    executable = (os.environ.get("CMR_GRAPHIC") or which("cmr-graphic")
                  or "/dev/shm/three-name-cmr-src/local/cmr-graphic")
    graphic = partial(is_graphic_cmr, executable=executable)
    result = exact_line([(p << 3) | g for p, g in zip(private, named)], *basis,
                        graphic=graphic)
    return None if result is None else list(result)
