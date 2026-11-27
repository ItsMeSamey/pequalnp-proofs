"""Search exact physical planes with a measured determinant degree."""
from functools import reduce
from itertools import combinations
from operator import xor
from determinant_degree import determinant_degree
from fixed_height import recognize, prior
from recognizer import tag_at

def solve(columns, dimension, selector_degree, height_degree):
    cert = recognize(columns, dimension, selector_degree, height_degree)
    degree = determinant_degree(columns, cert)
    missing = dimension - len(cert.anchors)
    cap = 2 * (missing + 2)
    limit = 2 * (degree // 2) + 1
    bits = 2 * dimension
    def candidates():
        if bits <= 2 * limit * (bits << (cap+1)).bit_length():
            yield from range(1 << bits)
            return
        points = prior['seeds'](bits, cap)
        for length in range(1, limit+1, 2):
            for used in combinations(points, length):
                yield reduce(xor, used)
    for chart in candidates():
        projected, lifted, support = {}, {}, []
        for idx, (key, tag, height) in enumerate(columns):
            if tag_at(chart, key, dimension) == tag:
                prior['add'](projected, key)
                if prior['add'](lifted, (key << 2) | height):
                    support.append(idx)
        if len(lifted) - len(projected) == 2:
            return support, missing, degree
    return None, missing, degree
