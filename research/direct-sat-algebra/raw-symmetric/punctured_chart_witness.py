"""Convert a recovered binary field algebra to polynomial coordinates deterministically."""
from dataclasses import dataclass
from punctured_witness import BinaryField, witness
from quadratic_centroid import zero_combinations
from quadratic_target import apply_basis, insert, reduce_vector


@dataclass
class PowerChart:
    field: BinaryField
    basis: tuple
    rows: dict

    def encode(self, element):
        rest, packed = reduce_vector(element, self.rows)
        if rest:
            raise ValueError("element outside binary algebra")
        return packed

    def decode(self, packed):
        return apply_basis(self.basis, packed)


def power_chart(m, one, multiply):
    """Construct a power basis from the coordinate unit and supplied field product.

    For each prime power p^a dividing m exactly, choose an element of degree
    p^a in its subfield. Their sum cannot be fixed by Frobenius^(m/p) for
    any p|m, hence generates the full field. All choices use linear kernels.
    """
    if m < 2 or not 0 < one < 1 << m:
        raise ValueError("invalid recovered field degree or unit")
    units = tuple(1 << i for i in range(m))
    if any(multiply(one, e) != e or multiply(e, one) != e for e in units):
        raise ValueError("invalid recovered algebra unit")
    def frobenius(x, k):
        for _ in range(k):
            x = multiply(x, x)
        return x
    n, p, generator = m, 2, 0
    while n > 1:
        if n % p:
            p += 1
            continue
        degree = 1
        while n % p == 0:
            n //= p
            degree *= p
        basis = zero_combinations(units, lambda x: x ^ frobenius(x, degree))
        choice = next((e for e in basis if frobenius(e, degree // p) != e), None)
        if not choice:
            raise ValueError("recovered algebra lacks the required subfield")
        generator ^= choice
        p += 1
    rows, powers, power = {}, [], one
    for i in range(m):
        if not insert(power, 1 << i, rows):
            raise ValueError("candidate generator has degree less than m")
        powers.append(power)
        power = multiply(power, generator)
    rest, relation = reduce_vector(power, rows)
    if rest:
        raise ValueError("power basis does not span")
    chart = PowerChart(BinaryField((1 << m) | relation), tuple(powers), rows)
    # Validate all basis products to certify the coordinate isomorphism.
    for i, a in enumerate(powers):
        for j, b in enumerate(powers):
            if chart.decode(chart.field.mul(1 << i, 1 << j)) != multiply(a, b):
                raise ValueError("recovered table does not define the certified field")
    return chart


def punctured_pair(chart, left_row, right_row, goal):
    """Return two elements in table coordinates from their hyperplane row masks."""
    field = chart.field
    if any(not 0 <= v < field.size for v in (left_row, right_row, goal)):
        raise ValueError("invalid packed form or target")
    trace_rows = {}
    for i in range(field.m):
        insert(field.trace_row(1 << i), 1 << i, trace_rows)
    def coefficient(row):
        encoded_row = sum(((row & vec).bit_count() & 1) << i for i, vec in enumerate(chart.basis))
        rest, coeff = reduce_vector(encoded_row, trace_rows)
        if rest:
            raise ArithmeticError("degenerate trace pairing")
        return coeff
    answer = witness(field, coefficient(left_row), coefficient(right_row), chart.encode(goal))
    return None if answer is None else tuple(chart.decode(x) for x in answer)


@dataclass
class WitnessChart:
    chart: object
    presentation: PowerChart
    offset: int
    original: tuple
    output_coords: object
    left_coords: object
    right_coords: object

    def solve(self, target):
        """Return an original input or None for the certified omitted target."""
        from quadratic_target import evaluate_anf
        if not 0 <= target < self.chart.field.size:
            raise ValueError("target outside original output dimension")
        goal = self.output_coords(target ^ self.offset)
        p = self.presentation
        pair = witness(p.field, p.encode(self.chart.trace_a), p.encode(self.chart.trace_b),
                       p.encode(goal))
        if pair is None:
            if goal:
                raise ArithmeticError("certified punctures missed a nonzero product")
            return None
        u, v = map(p.decode, pair)
        x = (apply_basis(self.chart.left, self.left_coords(u ^ 1)) ^
             apply_basis(self.chart.right, self.right_coords(v ^ 1)))
        if evaluate_anf(*self.original, x) != target:
            raise ArithmeticError("lifted input misses original target")
        return x


def prepare(n, m, constant, linear, pairs, *, known_offset=None):
    """Recover a field chart and preprocess the inverse chart maps."""
    from punctured_chart import coordinates, recover
    if known_offset is not None and not 0 <= known_offset < 1 << m:
        raise ValueError("known shift outside output space")
    shift = 0 if known_offset is None else known_offset
    chart = recover(n, m, constant ^ shift, linear, pairs, unknown_output_shift=known_offset is None)
    if chart is None:
        return None
    return WitnessChart(chart, power_chart(m, 1, chart.field.mul),
                        shift ^ chart.output_offset, (constant, tuple(linear), dict(pairs)),
                        coordinates(chart.output_basis), coordinates(chart.left_images),
                        coordinates(chart.right_images))


def check():
    from random import Random
    from quadratic_centroid import independent
    from quadratic_target import affine_domain, interpolate
    rng = Random(892)
    def basis(k):
        result = ()
        while len(result) < k:
            result = independent((*result, rng.randrange(1 << k)))
        return result
    tested = 0
    for modulus in (7, 11, 19, 67):
        field = BinaryField(modulus)
        m, n = field.m, 2*(field.m-1)
        ib, ob = basis(n), basis(m)
        a, b = rng.randrange(1, field.size), rng.randrange(1, field.size)
        h, left, _ = affine_domain(m, [(field.trace_row(a), 1)])
        k, right, _ = affine_domain(m, [(field.trace_row(b), 1)])
        shift, offset = rng.randrange(1 << n), rng.randrange(1, field.size)
        def original(x):
            z = apply_basis(ib, x ^ shift)
            u = h ^ apply_basis(left, z & ((1 << (m-1))-1))
            v = k ^ apply_basis(right, z >> (m-1))
            return offset ^ apply_basis(ob, field.mul(u, v))
        anf = interpolate(original, n)
        image = {original(x) for x in range(1 << n)}
        for supplied in (offset, None):
            chart = prepare(n, m, *anf, known_offset=supplied)
            assert chart is not None
            for t in range(1 << m):
                x = chart.solve(t)
                assert (x is not None) == (t in image)
                if x is not None:
                    assert original(x) == t
                tested += 1
    print(f"{tested} hidden field targets passed with supplied and recovered offsets")


if __name__ == "__main__":
    check()
