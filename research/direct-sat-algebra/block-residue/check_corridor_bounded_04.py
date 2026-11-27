"""Bounded original NAND oracle for scheduler04; exhaust two raw primary bits."""
from itertools import product
from corridor_nand import compile_objective, corridor_witness, solve_compiled


def evaluate(raw, gates):
    wires = list(raw)
    for x, y in gates:
        wires.append(int(not (wires[x] and wires[y])))
    return wires


def main():
    gates = ((0, 1), (2, 2))
    groups = ((0,),)
    expose = tuple((i, -i) for i in (1, 2, 3))
    for pins_word in product((None, 0, 1), repeat=4):
        pins = tuple((i, bit) for i, bit in enumerate(pins_word) if bit is not None)
        for eq in ((), ((0, 3, 1),)):
            opts = dict(clauses=expose, pins=pins, equalities=eq)
            src = compile_objective(2, gates, **opts)
            valid = []
            for raw in product((0, 1), repeat=2):
                w = evaluate(raw, gates)
                ok = all(w[i] == v for i,v in pins) and all(w[x]^w[y] == v for x,y,v in eq)
                assert evaluate(raw, src[1])[src[2]] == ok
                if ok:
                    valid.append(raw)
            assert corridor_witness(2, gates, groups, **opts)[0] == "skip"
            for status, raw in (corridor_witness(2, gates, groups, max_bad=1, **opts),
                                solve_compiled(src, 2, groups, max_bad=1, **opts)):
                assert status == ("sat" if valid else "unsat")
                assert raw in valid if valid else raw is None
    assert corridor_witness(2, gates, ())[0] == "skip"
    assert corridor_witness(2, gates, ((0,), (0,)))[0] == "skip"
    assert corridor_witness(2, gates, groups, pins=((3,1),))[0] == "sat"
    assert solve_compiled((2, gates, 2), 2, groups)[0] == "skip"
    print("bounded physical NAND corridor checks passed")


if __name__ == "__main__":
    main()
