"""Reconstruct an optional-rotation setting joining two passive-layer roots."""
from rooted_cutrank import solve, split
from trajectories import fixture, orbits, switch


def route(n, gates, feedback, roots, order=None):
    """The split tree bisects the supplied gate order; result is a gate bit mask."""
    first, second = roots
    if first == second:
        return 0
    baseline, chords, passive = fixture(n, gates, feedback)
    reference = baseline.copy()
    twist = 0
    for index, chord in enumerate(chords):
        labels, _ = orbits(reference)
        if labels[chord[0]] != labels[chord[1]]:
            switch(reference, chord)
            twist |= 1 << index
    labels, cycles = orbits(reference)
    component = labels[passive + first]
    if labels[passive + second] != component:
        return None
    positions = {vertex: pos for pos, vertex in enumerate(cycles[component])}
    def interlaces(edge, other):
        low, high = sorted(positions[v] for v in edge)
        return (low < positions[other[0]] < high) != (low < positions[other[1]] < high)
    if order is None:
        order = range(len(gates))
    order = list(order)
    if sorted(order) != list(range(len(gates))):
        raise ValueError("order must permute the gates")
    active = [g for g in order if chords[2*g][0] in positions]
    if not active:
        return 0
    indices = [2*g+i for g in active for i in range(2)]
    local = [chords[i] for i in indices]
    local_twist = sum(((twist >> i) & 1) << j for j, i in enumerate(indices))
    rows = [sum(1 << j for j, f in enumerate(local) if interlaces(e, f)) for e in local]
    mark = (passive + first, passive + second)
    target = sum(1 << j for j, f in enumerate(local) if interlaces(mark, f))
    result = solve(rows, target, local_twist, split(range(len(active))))
    if result is None:
        return None
    physical = result[0] ^ local_twist
    return sum(((physical >> (2*j)) & 1) << g for j, g in enumerate(active))
