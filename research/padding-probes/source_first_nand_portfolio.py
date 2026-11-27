"""Run sparse source shortcuts before the NAND portfolios and complete cover."""
from collections.abc import Mapping

from source_chart_cover_portfolio import solve as chart_portfolio
from source_mixed_nand_portfolio import solve as nand_portfolio


def solve(n, clauses, *, source_pins=(), exact_twice=False, stages=None, prepass=True,
          node_cap=None, nand_branch_cap=None, mixed=True):
    """Use requested physical stages once. Preserve per-backend budget meanings."""
    if type(mixed) is not bool:
        raise ValueError("mixed must be boolean")
    for cap in (node_cap, nand_branch_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("invalid search budget")
    rows = tuple(tuple(row) for row in clauses)
    items = source_pins.items() if isinstance(source_pins, Mapping) else source_pins
    pins = tuple(tuple(pin) for pin in items)
    front = chart_portfolio(n, rows, source_pins=pins, exact_twice=exact_twice,
                           stages=stages, prepass=prepass, node_cap=0)
    if front["status"] != "UNKNOWN":
        return front
    answer = nand_portfolio(n, rows, source_pins=pins, exact_twice=exact_twice,
                            stages=(), prepass=False, node_cap=node_cap,
                            nand_branch_cap=nand_branch_cap, mixed=mixed)
    return dict(answer, attempts=[*front["attempts"], *answer["attempts"]])
