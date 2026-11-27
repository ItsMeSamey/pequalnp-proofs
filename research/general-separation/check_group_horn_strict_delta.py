"""Strict alias refusals and actual ordered image replays."""
from ring_image_group_horn_strict import decide, solve_sparse, solve_tuples
from read_two_ring_nonzero import compile_nonzero


def reject(call, *args, **kwargs):
    try:
        call(*args, **kwargs)
    except ValueError:
        return
    raise AssertionError("malformed alias accepted")


def main():
    checks = 0
    for bad in (True, 1.0):
        for pair in ((1, bad), (bad, 1)):
            reject(solve_sparse, [pair])
            reject(solve_sparse, [], labels=iter(pair))
            reject(solve_tuples, [], labels=iter(pair))
            reject(solve_tuples, [(pair, [])])
            reject(solve_tuples, [((3,), pair)])
            checks += 5
    for rows, expected in (([(1, 1)], "nonzero"), ([(1,), (-1,)], "zero")):
        raw = compile_nonzero(1, rows)
        result = decide(*(raw[key] for key in ("n", "clauses", "point", "k")))
        assert result["status"] == expected
        if expected == "nonzero":
            assert result["assignment"] == (1,)
    print(f"{checks} strict alias refusals and two physical image controls passed")


if __name__ == "__main__":
    main()
