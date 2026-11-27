"""Count uncovered endpoint-compatible colorings by affine inclusion–exclusion."""


def uncovered_count(vertices, endpoint, edges, alternatives, pins=()):
    def encode(edge):
        u, v, tag = edge
        if not (0 <= u < vertices and 0 <= v < vertices and 0 <= tag < 4):
            raise ValueError("invalid tagged edge")
        key = (1 << u) ^ (1 << v)
        return key, [(key << (bit * vertices), (tag >> bit) & 1) for bit in range(2)]

    encoded = [encode(edge) for edge in edges]
    demand, base = encode(endpoint)
    for vertex, bit, value in pins:
        if not (0 <= vertex < vertices and bit in (0, 1) and value in (0, 1)):
            raise ValueError("invalid pin")
        base.append((1 << (bit * vertices + vertex), value))
    systems = []
    for route in alternatives:
        route = tuple(route)
        if len(set(route)) != len(route):
            raise ValueError("route must be a subset")
        key, rows = 0, []
        for i in route:
            if not 0 <= i < len(encoded):
                raise ValueError("invalid indexed edge")
            k, equations = encoded[i]
            key ^= k
            rows.extend(equations)
        if key != demand:
            raise ValueError("incorrect route boundary")
        systems.append(rows)

    def solutions(rows):
        pivots = {}
        for x, rhs in rows:
            while x:
                i = x.bit_length() - 1
                if i not in pivots:
                    pivots[i] = x, rhs
                    break
                old, val = pivots[i]
                x ^= old
                rhs ^= val
            else:
                if rhs:
                    return 0
        return 1 << (2 * vertices - len(pivots))

    count = 0
    for mask in range(1 << len(systems)):
        equations = base.copy()
        for i, rows in enumerate(systems):
            if mask >> i & 1:
                equations.extend(rows)
        term = solutions(equations)
        count += -term if mask.bit_count() & 1 else term
    return count
