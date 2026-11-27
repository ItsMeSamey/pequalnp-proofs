"""Find colors invalidating all proposed physical representatives of a virtual edge."""
from itertools import product


def bad_coloring(vertex_count, endpoint, edges, alternatives):
    """Return vertex colors for a failed cover, or None. Also check physical boundaries."""
    def key(edge):
        u, v, tag = edge
        if not (0 <= u < vertex_count and 0 <= v < vertex_count and 0 <= tag < 4):
            raise ValueError("edge lies outside the declared graph or tag alphabet")
        return (1 << u) ^ (1 << v)

    demand = key(endpoint)
    keys = [key(edge) for edge in edges]
    choices = []
    for route in alternatives:
        parity = 0
        candidates = []
        route = tuple(route)
        if len(set(route)) != len(route):
            raise ValueError("route must be an indexed subset")
        for i in route:
            if not 0 <= i < len(keys):
                raise ValueError("invalid physical index")
            parity ^= keys[i]
            for bit in (0, 1):
                candidates.append((keys[i] << (bit * vertex_count), 1 ^ ((edges[i][2] >> bit) & 1)))
        if parity != demand:
            raise ValueError("physical boundary differs from virtual boundary")
        choices.append(candidates)

    endpoint_rows = [(demand << (bit * vertex_count), (endpoint[2] >> bit) & 1) for bit in (0, 1)]
    for selection in product(*choices):
        pivots = {}
        for row, rhs in (*endpoint_rows, *selection):
            while row:
                i = row.bit_length() - 1
                if i not in pivots:
                    pivots[i] = row, rhs
                    break
                previous, target = pivots[i]
                row ^= previous
                rhs ^= target
            else:
                if rhs:
                    break
        else:
            x = 0
            for i in sorted(pivots):
                row, rhs = pivots[i]
                x |= (rhs ^ ((row & x).bit_count() & 1)) << i
            return [((x >> i) & 1) + 2*((x >> (i+vertex_count)) & 1) for i in range(vertex_count)]
    return None
