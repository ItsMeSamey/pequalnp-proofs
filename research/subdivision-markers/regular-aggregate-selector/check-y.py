"""Exhaustive zero-trace checks on sampled rank-two limbs of mobile rank at most one."""


def span(columns):
    values = {0}
    for col in columns:
        values |= {x ^ col for x in values}
    return values


def parity(a, b):
    return (a & b).bit_count() % 2


def run():
    seed = 43

    def draw(n):
        nonlocal seed
        seed = (1664525 * seed + 1013904223) % (1 << 32)
        return (seed >> 11) % n

    limbs = states = missing = overlap = 0
    for _ in range(55):
        k = 2 + draw(3)
        coloop_types = [1 + draw(3) for _ in range(k)]
        mobile_type = draw(4)
        columns = [1 << i for i in range(k)] + [j << k for j in (1, 2, 3)]
        port = [sum(((h >> j) & 1) << i for i, h in enumerate(coloop_types))
                ^ (((mobile_type >> j) & 1) << k) for j in range(2)]
        physical = [0, *port, port[0] ^ port[1]]
        if len(set(physical)) != 4:
            continue
        index = {v: j for j, v in enumerate(physical)}
        attainable = [set() for _ in range(16)]
        # A mask per channel, without using a fundamental-basis parametrization.
        totals = [0]
        for c in columns:
            totals.extend([v ^ c for v in totals])
        traces = {}
        for zero_mask in range(1 << len(columns)):
            zero_span = span(c for i, c in enumerate(columns) if zero_mask >> i & 1)
            if len(zero_span) == 1 << zero_mask.bit_count():
                traces[zero_mask] = sum(1 << j for j, v in enumerate(physical) if v in zero_span)
        full = (1 << len(columns)) - 1
        for c, first in enumerate(totals):
            if first not in index:
                continue
            for d, second in enumerate(totals):
                if second not in index:
                    continue
                trace = traces.get(full ^ (c | d))
                if trace is not None:
                    attainable[index[first] | (index[second] << 2)].add(trace)
        for sigma, choices in enumerate(attainable):
            first, second = sigma & 3, sigma >> 2
            least = sum(1 << u for u in range(4)
                        if not parity(u, mobile_type) and
                        all(not parity(u, h) or not (parity(first, h) or parity(second, h))
                            for h in coloop_types))
            assert least in choices
            assert all((trace & least) == least for trace in choices)
            # Realize the torso proxy directly: omit missing types, use a
            # parallel pair on the mobile type, and one leg on a coloop-only type.
            active = sorted(set(coloop_types) | ({mobile_type} if mobile_type else set()))
            included = [h for h in active if h != mobile_type and
                        not (parity(first, h) or parity(second, h))]
            zero_spokes = span(1 << active.index(h) for h in included)
            proxy = sum(1 << u for u in range(4) if
                        sum(parity(u, h) << j for j, h in enumerate(active)) in zero_spokes)
            assert proxy == least
            states += 1
        limbs += 1
        missing += len(active) == 2
        overlap += mobile_type != 0 and mobile_type in coloop_types
    print("limbs, imbalances, missing type, shared mobile/coloop type:",
          limbs, states, missing, overlap)


if __name__ == "__main__":
    run()
