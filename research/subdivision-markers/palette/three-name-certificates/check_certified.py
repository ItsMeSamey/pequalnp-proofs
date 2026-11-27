from functools import partial
from random import Random
import sys
from certified_graphic import find_obstruction, graphic_or_obstruction, is_graphic_certified
from minor_check import _TARGETS, verify_minor
from check_line import direct
from exact_line import exact_line

if __name__ == "__main__":
    path = sys.argv[1]
    decide = partial(graphic_or_obstruction, executable=path)
    rng = Random(4759)
    for name, target in _TARGETS.items():
        new = 1 << max(x.bit_length() for x in target)
        source = [0, new, target[0] ^ new, *target[1:], target[1]]
        cert = decide(source)
        assert cert and cert.target == name and cert.contract and cert.delete
        assert verify_minor(source, cert.retain, cert.contract, cert.delete, name)
        assert not verify_minor(source, cert.retain, cert.delete, cert.contract, name)
        print(name, "retain", cert.retain, "contract", cert.contract, "delete", cert.delete)
    assert decide([0,1,2,3,3]) is None
    try:
        find_obstruction([1,2,3], lambda _: False)
    except ValueError:
        pass
    else:
        raise AssertionError("accepted a fake CMR negative")
    terminal_verdicts = []
    def observe(columns):
        verdict = decide(columns)
        terminal_verdicts.append(None if verdict is None else verdict.target)
        return verdict is None
    assert exact_line([8,9],1,2,4,graphic=observe) == (0,1)
    assert "F7" in terminal_verdicts
    terminal_verdicts.clear()
    assert exact_line([2,3],1,2,4,graphic=observe) is None
    assert terminal_verdicts == [None]
    for _ in range(32):
        n = rng.randrange(4,9)
        cols = [rng.randrange(32) for _ in range(n)]
        pins = tuple(i for i in range(n) if rng.randrange(6) == 0)
        result = exact_line(cols,1,2,4,forced=pins,graphic=partial(is_graphic_certified,executable=path))
        assert (result is not None) == direct(cols,pins)
    print("four original-index minors, forged negative rejection and 34 certified line cases passed")
