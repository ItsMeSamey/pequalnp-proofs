"""Two dependent cut slopes with incompatible prefix noise."""
from check_binary_fault_solver import Source
from syndrome_tail_range import _candidate, recognize


def check():
    # Raw order u,t.  At suffix width one both t and t XOR u have slope 1.
    for operation, expected, correct_rank in (
        ("xor", (0, 2), 1),
        ("nand", (1, 2), 2),
        ("both", (1, 0), 2),
    ):
        circuit = Source(2)
        noisy = circuit.xor(1, 0)
        out = getattr(circuit, operation)(1, noisy)
        source = circuit.finish(out)
        assert _candidate(2, source, 1) is None
        model = recognize(2, source)
        assert (model.tail_width, model.m) == (2, correct_rank)
        assert tuple(model.range_count(2*u, 2*u+1) for u in (0, 1)) == expected


if __name__ == "__main__":
    check()
