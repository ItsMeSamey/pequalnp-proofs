"""Small original-word controls for exact masked majority. Execution belongs to 04."""
from check_binary_fault_solver import Source, raw
from forecast_consistency_search import threshold
from odd_masked_circuit import compile_source
from tail_range_forecast import TailRangeForecast, posterior


def fixture(r, truth):
    """Build the displayed source for each truth table on zero or one bit."""
    m = r + 4
    c = Source(m)
    if r == 0:
        phi = -2 if truth else -1
        ones = -2
    else:
        assert r == 1 and 0 <= truth < 4
        phi = (-1, c.inv(3), 3, -2)[truth]
        ones = 3
    left = c.both(c.inv(0), phi)
    right = c.both(0, c.both(ones, m - 1))
    union = c.nand(c.inv(left), c.inv(right))
    return c.finish(c.both(c.both(1, 2), union))


def raw_table(h, circuit):
    """Bit i is the NAND output on original raw word i, with no decoder use."""
    size = 1 << h
    full = (1 << size) - 1
    wires = {-1: 0, -2: full}
    for site in range(h):
        run = 1 << (h - site - 1)
        column = ((1 << run) - 1) << run
        filled = 2 * run
        while filled < size:
            column |= column << filled
            filled *= 2
        wires[site] = column
    gates, out = circuit
    for index, (left, right) in enumerate(gates, h):
        wires[index] = full ^ (wires[left] & wires[right])
    return wires[out]


def check(r, truth):
    m = r + 4
    h = 4 * m
    latent_budget = 1 << m
    planted = latent_budget - 1
    count = truth.bit_count()
    source = fixture(r, truth)
    masked = compile_source(m, source)
    source_models = 2 * count + 1
    assert sum(raw(m, source, x) for x in range(1 << m)) == source_models
    ones = raw_table(h, masked)
    assert ones.bit_count() == (1 << (3 * m)) * source_models
    assert raw(h, masked, planted) == 1

    stages = [(masked, None)]
    stages += [(threshold(h, (1 << k) - 1), k) for k in reversed(range(m, h))]
    final = threshold(h, 1 << (m - 1))
    cap = max(len(q[0]) for q, _ in stages + [(final, None)])
    learner = TailRangeForecast(h, cap, max_latents=latent_budget)
    live = (1 << (1 << h)) - 1
    history = ()

    def verify(q, mask, expected):
        zero, one = live & ~mask, live & mask
        assert (zero.bit_count(), one.bit_count()) == expected
        result = posterior(h, history, q, max_latents=latent_budget)
        assert result["status"] == "exact" and result["counts"] == expected
        assert all(k is None or k <= m for k in result["latent_widths"])
        for bit, (group, word) in enumerate(zip((zero, one), result["witnesses"])):
            if group:
                assert word is not None and (group >> word) & 1
                assert raw(h, q, word) == bit
                assert all(raw(h, previous, word) == b for previous, b in history)
            else:
                assert word is None
        assert learner.predict(q) == result["prediction"] == int(expected[1] > expected[0])

    for q, k in stages:
        if k is None:
            mask = ones
            positive = (1 << (3 * m)) * source_models
            expected = ((1 << h) - positive, positive)
            assert expected[0] > expected[1]
        else:
            mask = (1 << (1 << k)) - 1
            half = (1 << (k - m)) * source_models
            expected = (half, half)
        verify(q, mask, expected)
        assert raw(h, q, planted) == 1 and learner.observe(q, 1) is True
        history += ((q, 1),)
        assert learner.history == history
        live &= mask
    assert len(history) == 1 + 3 * m
    verify(final, (1 << ((1 << (m - 1)) + 1)) - 1, (1, 2 * count))
    assert raw(h, final, planted) == 0
    assert learner.observe(final, 0) == bool(count)


if __name__ == "__main__":
    for r in (0, 1):
        for truth in range(1 << (1 << r)):
            check(r, truth)
    print("Every strict SAT verdict, true-history tie and original assignment bin agrees.")
