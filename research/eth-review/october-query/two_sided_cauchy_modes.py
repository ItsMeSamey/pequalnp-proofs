"""Two-sided separated expansion of a D.1 crossing tile at its birth precision."""
from math import comb, factorial


def mode_weight(k):
    """Universal dyadic valuation on the target, including the Cauchy prefactor."""
    if k < 0:
        raise ValueError("negative mode")
    return 1 + k + 2 * (k - k.bit_count())


def target_modes(K, A, length, precision, *, one, add, mul, scale, inverse_unit):
    """Yield (k, target coefficient) in the caller's native ring.

    K is the TRUE native virtual-column W[x,y0], A=2^(i+1)/(T-y0+x).
    Both come from native geometry; evenness alone does not justify this cutoff. inverse_unit operates in
    the caller's actual (possibly unramified, V-truncated) birth ring.
    length bounds 1+max(real j); zero-projection modes may be skipped later.
    """
    if length < 0 or precision < 1:
        raise ValueError("invalid length or precision")
    numerator = K
    reverse_denominator = one
    for k in range(length):
        if mode_weight(k) >= precision:
            break
        reverse_denominator = mul(reverse_denominator,
                                  inverse_unit(add(one, scale(A, -k))))
        target = mul(numerator, reverse_denominator)
        yield k, scale(target, (1 - 2*k*k) << (k - k.bit_count()))
        numerator = mul(numerator, add(A, scale(one, -2*k)))


def column_mode(j, k, precision):
    """Integer residue multiplying a real Boolean column, before casting to ring."""
    if min(j, k) < 0 or precision < 1:
        raise ValueError("invalid mode coordinate or precision")
    if j < k:
        return 0
    modulus = 1 << precision
    odd_factorial = factorial(k) >> (k - k.bit_count())
    numerator = comb(j, k) * odd_factorial
    denominator = 1
    for r in range(1, k + 1):
        denominator = denominator * (1 - 2*r*j) % modulus
    return numerator * pow(denominator, -1, modulus) % modulus


def row_tile_sum(K, A, real_columns, precision, *, zero, one, add, mul, scale,
                 inverse_unit):
    """Sum the crossing contribution for real (j, Boolean bit) column pairs."""
    columns = tuple(real_columns)
    if any(j < 0 or bit not in (0, 1) for j, bit in columns):
        raise ValueError("invalid tile read")
    if len({j for j, _ in columns}) != len(columns):
        raise ValueError("duplicate tile coordinate")
    length = 1 + max((j for j, _ in columns), default=-1)
    answer = zero
    for k, target in target_modes(K, A, length, precision, one=one, add=add,
                                  mul=mul, scale=scale, inverse_unit=inverse_unit):
        moment = sum(column_mode(j, k, precision) for j, bit in columns if bit)
        answer = add(answer, scale(target, moment))
    return answer


def native_entries(L, t, zeta, precision, *, one, add, mul, scale, inverse_unit):
    """Construct call-local W(x,y) and crossing (K,A)(x,y0) for this sample.

    Integer constants embed via scale(one, n); no nonunit is inverted, including
    when zeta is zero. Virtual y0 is allowed even if that slot has no real port.
    """
    from fractions import Fraction
    if L < 2 or L & (L-1) or not -L < t < L or t == 0 or precision < 1:
        raise ValueError("expected nonzero nonendpoint source center")
    modulus = 1 << precision
    level = (abs(t) & -abs(t)).bit_length()-1
    alpha = 2*L

    def integer_ratio(n, d):
        q = Fraction(n, d)
        return q.numerator * pow(q.denominator, -1, modulus) % modulus

    eta = integer_ratio((-1 if t % 2 else 1)*factorial(L+t)*factorial(L-1-t),
                        factorial(L)*factorial(L-1))
    grid = range(-L, L)
    factors = {s:add(one, scale(zeta, integer_ratio(alpha, t-s)))
               for s in grid if s != t}
    diagonal = scale(one, eta)
    for value in factors.values():
        diagonal = mul(diagonal, value)

    def weight(x, y):
        if not (0 <= x < L and 0 <= y < L):
            raise ValueError("slot outside packet")
        q = y-x
        if q == t:
            return diagonal
        shift = scale(zeta, integer_ratio(alpha, t-q))
        return mul(mul(diagonal, shift), inverse_unit(factors[q]))

    def crossing(x, y0):
        if not 0 <= y0 < (1 << (level+1)) or ((x^y0) >> level) & 1:
            raise ValueError("expected crossing row and tile")
        q = y0-x
        K = weight(x, y0)
        A = scale(inverse_unit(factors[q]), integer_ratio(1 << (level+1), t-q))
        return K, A

    return weight, crossing
