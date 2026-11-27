"""Exact ordered training sweep followed by survivor-based ordered trial scores."""
from itertools import product
from operator import index

from late_moment_decoder import decode
from ordered_score_stream import OrderedScores


def ordered_handoff(m, length, base, score, *, rounds, max_atoms, max_lists,
                    models=None, observe=None):
    """Return (model_count, winning_lists_and_scores, surviving_atoms), or None.

    rounds includes training. score(row) is called only during training. Each
    sweep visits every original ordered list, even when all scores tie.
    observe(stage,row,value), if supplied, sees every scored trial in order.
    max_lists caps all sweeps together; max_atoms bounds decoder order/work.
    A decoding refusal can occur after the training sweep was observed.
    """
    m, length, base, rounds, max_atoms, max_lists = map(
        index, (m, length, base, rounds, max_atoms, max_lists))
    if min(m, rounds) < 1 or min(length, base, max_atoms, max_lists) < 0:
        raise ValueError("invalid handoff parameters")
    if models is not None:
        models = index(models)
        if not 0 <= models <= base:
            raise ValueError("invalid model count")
    if rounds*(2*m)**length > max_lists:
        return None
    order = min(length, 2*max_atoms + int(models is None))
    stream = OrderedScores(m, length, base, order=order)

    def lists():
        return product(product(range(m), range(2)), repeat=length)

    def mask_of(row):
        mask = 0
        for i, c in row:
            mask ^= c << i
        return mask

    for row in lists():
        value = score(row)
        stream.feed(row, value)
        if observe is not None:
            observe(0, row, value)
    moments, winner, best = stream.finish()
    profile = decode(m, moments, models)
    if profile is None:
        return None
    model_count, atoms = profile
    winners = []
    for stage in range(rounds):
        if stage:
            winner = best = None
            for row in lists():
                mask = mask_of(row)
                value = model_count + sum(mass for word, mass in atoms.items()
                                          if (word & mask).bit_count() % 2 == 0)
                if observe is not None:
                    observe(stage, row, value)
                if best is None or value < best:
                    best, winner = value, row
        mask = mask_of(winner)
        atoms = {word: mass for word, mass in atoms.items()
                 if (word & mask).bit_count() % 2 == 0}
        if model_count + sum(atoms.values()) != best:
            raise ValueError("profile disagrees with the winning score")
        winners.append((winner, best))
    return model_count, tuple(winners), atoms
