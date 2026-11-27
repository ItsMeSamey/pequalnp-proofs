"""Original 3CNF witness via deterministic physical-shell dimension dispatch."""

from cnf_shell import compile_cnf
from shell_dispatch import dispatch_block_witness


def cnf_dispatch_witness(n, clauses, *, encoding="direct"):
    """Return a satisfying assignment of the declared variables or None."""
    chart = compile_cnf(n, clauses, encoding=encoding)
    if chart is None:
        return None
    raw = dispatch_block_witness(chart.shells, chart.pins)
    return None if raw is None else chart.decode(raw)
