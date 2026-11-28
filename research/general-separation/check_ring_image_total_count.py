"""Independent original Boolean assignments and exact modular normalization."""
from itertools import product
from read_two_ring_nonzero import compile_nonzero
from ring_image_total_count import count


def data(a, rows):
    raw = compile_nonzero(a, rows)
    words = tuple(raw[z] for z in ("n", "clauses", "point", "k"))
    models = {bits for bits in product((0, 1), repeat=a)
              if all(any(bits[abs(x)-1] == (x > 0) for x in row) for row in rows)}
    residue = (-15)**raw["expanded_edges"] * len(models) % 3**raw["k"]
    return words, models, residue


def verify(result, models, residue):
    assert result["count"] == len(models) and result["value"] == residue
    assert result["status"] == ("nonzero" if models else "zero")
    if models:
        assert result["assignment"] in models


def main():
    words, models, residue = data(5, [(-2,), (3, -3)])
    result = count(*words, max_assignments=2)
    verify(result, models, residue)
    assert (result["count"], result["assignments"], result["backend"]) == (16, 2, "source")
    assert count(*words, max_assignments=1)["status"] == "unknown"
    words, models, residue = data(2, [(1,), (-1,)])
    verify(count(*words), models, residue)
    rows = [(1,2), (2,3), (3,4), (4,1), (-1,-2), (-2,-3), (-3,-4), (-4,-1)]
    words, models, residue = data(4, rows)
    fast = count(*words, max_assignments=0)
    verify(fast, models, residue)
    assert fast["backend"] == "planar"
    fallback = count(*words, max_determinants=1)
    verify(fallback, models, residue)
    assert fallback["backend"] == "source" and fallback["determinants"] == 1
    denied = count(*words, max_assignments=15, max_determinants=1)
    assert denied["status"] == "unknown" and denied["required_log2"] == 4
    assert denied["planar_attempt"]["determinants"] == 1
    assert count(0, (), (), 1)["status"] == "off_image"
    for bad in (True, -1, 1.5):
        try:
            count(*words, max_determinants=bad)
        except ValueError:
            continue
        raise AssertionError("invalid cap")
    print("unused variables, SAT/UNSAT, off-image, cap refusal and both exact branches passed")


if __name__ == "__main__":
    main()
