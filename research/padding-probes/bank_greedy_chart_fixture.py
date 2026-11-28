"""Physical pair-bank greedy gap beyond the original chart and Horn on its SAT member."""
def chart_gap(*, unsat=False):
    if type(unsat) is not bool:
        raise ValueError("unsat must be Boolean")
    rows = [(1,2,3), (1,2,4), (1,3,5), (2,4,6)]
    for i, a in ((4,7),(6,8)):
        rows.extend(((-i,a),(-i,-a)))
    for j in (1,2,3,5):
        rows.extend(((j,9),(-j,9)))
    rows.append((-9,-2 if unsat else 2))
    return 9, tuple(rows)
