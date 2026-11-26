"""Binary three-port reduction, with a callable rooted three-circuit witness oracle."""
from itertools import combinations
from solve import canonical, eliminate, image, solve


def basis_for(port, predicate):
    for coords in combinations(range(1, 8), 3):
        if len(canonical(coords)) == 3 and predicate(coords):
            return tuple(image(port, mask) for mask in coords)
    raise AssertionError("no admissible terminal basis in a three-space")


def dual_representation(cols):
    _, relations = eliminate(cols)
    return tuple(sum(((w >> j) & 1) << i for i, w in enumerate(relations))
                 for j in range(len(cols)))


def three_witness(local, port, coord, f, circuit):
    """Handle one mixed orthogonal state, using at most two triple witness calls.

    circuit(ordinary, terminals) returns the local ordinary membership bitmask of
    a single circuit containing the three extra terminals, or None.
    """
    ids, cols = zip(*local)
    n = len(cols)
    u = image(port, coord)
    basis = basis_for(port, lambda b: b[0] ^ b[1] ^ b[2] == coord)
    mask = circuit(cols, basis)
    if mask is None:
        basis = basis_for(port, lambda b: all((x & f).bit_count() % 2 for x in b))
        dual = dual_representation(cols + basis)
        dual_mask = circuit(dual[:n], dual[n:])
        if dual_mask is None:
            return None
        available = [i for i in range(n) if not dual_mask >> i & 1]
        take = solve(tuple(cols[i] for i in available), u)
        assert take is not None
        mask = sum(1 << i for j,i in enumerate(available) if take >> j & 1)
    return sum(1 << idx for j,idx in enumerate(ids) if mask >> j & 1)
