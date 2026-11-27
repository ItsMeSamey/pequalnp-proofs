"""Physical nonbottom-restoration control for the byte and marker event charts."""
from event_fixtures import _small_bags, _slot_offsets
from padding_cnf import encode
from stack_align_padding import _comparator


def saved_top():
    """The only two pinned physical keys are 45 (accept) and 47 (reject).

    Slot order is w,a,b,c,d,enable.  The raw machine saves w, a and b,
    compares c to b and d to the recovered a; w remains stacked at EOF.
    The immutable challenge forms part of the scanned original byte prefix.
    """
    challenge = [(1, -2, 4), (-3, 4, 5)]
    n = 5
    aliases = [-307, 19, -821, -821, 5, 97]
    occurrence_pins = ((0, 1), (4, 0), (5, 1))
    id_pins = ((821, 0),)
    actions = ("push", "push", "push", "pop", "pop", "gate")
    table, initial, bottom, outputs = _comparator(challenge, actions)
    positions, length = _slot_offsets(challenge, n)
    macro_schedule = ("push", "push", "push", "pop", "pop", "stay")
    schedule = {positions[i]: op for i, op in enumerate(macro_schedule) if op != "stay"}
    edges = {(i, i + 1) for i in range(length)}
    edges.update(((positions[1], positions[4]), (positions[2], positions[3])))
    bags, tree_edges = _small_bags(length + 1, edges, None)
    return dict(challenge=challenge, n=n, aliases=aliases, table=table, initial=initial,
                bottom=bottom, outputs=outputs, occurrence_pins=occurrence_pins,
                id_pins=id_pins, schedule=schedule, macro_schedule=macro_schedule,
                slot_events=positions, bags=bags, tree_edges=tree_edges,
                raw_witnesses={1: encode(challenge, n, 45), 0: encode(challenge, n, 47)})
