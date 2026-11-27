"""Recognize constant private directions having bounded-degree active selectors over F2."""
from dataclasses import dataclass
from itertools import combinations

@dataclass(frozen=True)
class Generator:
    site: int
    free_monomial: int

@dataclass
class Certificate:
    dimension: int
    degree: int
    generators: list
    anchors: list

def subset_masks(positions, maximum_size):
    for size in range(min(maximum_size, len(positions)) + 1):
        for support in combinations(positions, size):
            yield sum(1 << j for j in support)

def tag_at(chart, key, dimension):
    first = (chart & key).bit_count() % 2
    second = ((chart >> dimension) & key).bit_count() % 2
    return first | (second << 1)

def bit_indices(bits):
    while bits:
        low = bits & -bits
        yield low.bit_length() - 1
        bits ^= low

def activation_terms(key, tag, dimension):
    first = [1 << j for j in bit_indices(key)]
    second = [1 << (dimension+j) for j in bit_indices(key)]
    if not tag & 1:
        first.append(0)
    if not tag & 2:
        second.append(0)
    return [a | b for a in first for b in second]

def recognize(columns, dimension, degree):
    """Input sites (private direction, two-bit tag, two-bit height), all as integers.

    Require compressed private coordinates. Returned generator bitsets select actual
    site indices, and are independent of their heights.
    """
    if dimension < 0 or degree < 1:
        raise ValueError("dimension must be nonnegative and degree positive")
    private_pivots = {}
    for key, tag, height in columns:
        if not (0 <= key < (1 << dimension) and 0 <= tag < 4 and 0 <= height < 4):
            raise ValueError("column outside declared coordinates")
        vector = key
        while vector:
            pivot = vector.bit_length()-1
            if pivot not in private_pivots:
                private_pivots[pivot] = vector
                break
            vector ^= private_pivots[pivot]
    if len(private_pivots) != dimension:
        raise ValueError("compress unobserved private directions first")

    # Every nonzero-key site has a codimension-two activation slice. In coordinates
    # adapted to it, every supported ANF factors as its two literals times a free ANF.
    generators = []
    monomial_ids = {}
    feature_pivots = {}
    constant_pivots = {}
    seen = set()
    for site,(key,tag,_) in enumerate(columns):
        if not key or (key,tag) in seen:
            continue
        seen.add((key,tag))
        if degree < 2:
            continue
        pivot = key.bit_length()-1
        free = [j for j in range(2*dimension) if j not in (pivot,pivot+dimension)]
        activation = activation_terms(key,tag,dimension)
        for monomial in subset_masks(free, degree-2):
            terms = set()
            for term in activation:
                product = monomial | term
                terms.symmetric_difference_update((product,))
            constant = key if 0 in terms else 0
            terms.discard(0)
            features = 0
            for product in terms:
                position = monomial_ids.setdefault(product,len(monomial_ids))
                features ^= key << (dimension*position)
            combination = 1 << len(generators)
            generators.append(Generator(site,monomial))
            while features:
                pivot = features.bit_length()-1
                if pivot not in feature_pivots:
                    feature_pivots[pivot]=(features,constant,combination)
                    break
                old,old_const,old_comb = feature_pivots[pivot]
                features ^= old
                constant ^= old_const
                combination ^= old_comb
            if features:
                continue
            while constant:
                pivot = constant.bit_length()-1
                if pivot not in constant_pivots:
                    constant_pivots[pivot]=(constant,combination)
                    break
                old_const,old_comb = constant_pivots[pivot]
                constant ^= old_const
                combination ^= old_comb
    return Certificate(dimension,degree,generators,list(constant_pivots.values()))

def selected_sites(certificate, columns, combination, chart):
    selected = set()
    for position in bit_indices(combination):
        generator = certificate.generators[position]
        key,tag,_ = columns[generator.site]
        if (chart & generator.free_monomial == generator.free_monomial
                and tag_at(chart,key,certificate.dimension) == tag):
            selected.symmetric_difference_update((generator.site,))
    return selected

def solve(columns, dimension, degree):
    """Return indices of an exact physical plane witness, or None."""
    from functools import reduce
    from operator import xor
    from pathlib import Path
    from runpy import run_path
    previous = run_path(str(Path(__file__).resolve().parents[1] / "pnp-chart-hitting.py"))
    certificate = recognize(columns, dimension, degree)
    bits = 2 * dimension
    cap = 2 * (dimension - len(certificate.anchors) + 2)
    max_length = 2 * degree + 1
    def candidate_charts():
        field_bits = (bits << (cap + 1)).bit_length()
        if bits <= 2 * max_length * field_bits:
            yield from range(1 << bits)
            return
        points = previous["seeds"](bits, cap)
        for length in range(1, max_length + 1, 2):
            for points_used in combinations(points, length):
                yield reduce(xor, points_used)
    add = previous["add"]
    for chart in candidate_charts():
        private, physical, witness = {}, {}, []
        for i, (key, tag, height) in enumerate(columns):
            if tag_at(chart, key, dimension) != tag:
                continue
            add(private, key)
            if add(physical, (key << 2) | height):
                witness.append(i)
        if len(physical) - len(private) == 2:
            return witness
    return None
