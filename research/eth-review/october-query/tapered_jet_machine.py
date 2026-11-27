"""Coordinatewise scalar Hermite reducer on the manuscript's complete grid."""
def valuation(x):
    return (abs(x) & -abs(x)).bit_length() - 1


def odd_part(x):
    return x >> valuation(x)


def inverse_odd(x, bits):
    result = 1
    width = 1
    while width < bits:
        width = min(2 * width, bits)
        result = result * (2 - x * result) % (1 << width)
    return result


def recover(a, u, m, p, coordinates, jet):
    """jet(t,j,coordinate,precision) returns the corresponding lifted residue."""
    assert m >= u and 1 <= u <= a and p >= 1
    length, alpha = 1 << a, 1 << (a + 1)
    h = (3 * m + u - 1) // u
    nodes = {t: h * (u - valuation(t)) for t in range(-length, length)
             if t and valuation(t) < u}

    def origin_valuation(t):
        return sum(n * (valuation(q) - valuation(t - q))
                   for q, n in nodes.items() if q != t)

    loss = max(0, max((n - 1) * (a + 1 - valuation(t)) - origin_valuation(t)
                      for t, n in nodes.items()))
    width = p + loss
    modulus = 1 << width
    accum = [0] * coordinates
    for t, n in nodes.items():
        v = origin_valuation(t)
        pt = p + 8 * h * (length >> valuation(t)) + 8 * m * (a + 1)
        mod_t = 1 << pt
        unit = 1
        local_factors = []
        for q, count in nodes.items():
            if q == t:
                continue
            delta = t - q
            ratio = odd_part(-q) * inverse_odd(odd_part(delta), width) % modulus
            unit = unit * pow(ratio, count, modulus) % modulus
            c = (alpha >> valuation(delta)) * inverse_odd(odd_part(delta), pt) % mod_t
            local_factors.append((c, count))
        for d in range(coordinates):
            row = [jet(t, j, d, pt) % mod_t for j in range(n)]
            for c, count in local_factors:
                for _ in range(count):
                    for j in range(1, n):
                        row[j] = (row[j] - c * row[j - 1]) % mod_t
            weight = unit
            for j, coeff in enumerate(row):
                shift = loss + v + j * (valuation(t) - a - 1)
                assert shift >= 0 and pt + shift >= width
                if shift < width:
                    accum[d] = (accum[d] + ((weight * coeff) << shift)) % modulus
                weight = weight * odd_part(-t) % modulus
    assert all(x % (1 << loss) == 0 for x in accum)
    return [x >> loss for x in accum]
