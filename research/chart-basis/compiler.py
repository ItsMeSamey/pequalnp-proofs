"""Compile acyclic guarded choices to a list of certified affine witness charts.

An affine form uses bit 0 for its constant, bit i+1 for variable i.
Guards and terminals list forms required to evaluate to one (disjunction).
Charts store equations required to evaluate to zero, then affine witness forms.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Chart:
    equations: tuple
    witness: tuple = ()


def form_value(form, assignment):
    return ((form & ((assignment << 1) | 1)).bit_count() & 1)


def normal(equations):
    pivots = {}
    for row in equations:
        while row > 1 and row.bit_length() in pivots:
            row ^= pivots[row.bit_length()]
        if row == 1:
            return None
        if row:
            pivots[row.bit_length()] = row
    return tuple(pivots.values())


def indicator(equations):
    terms = {0}
    for row in equations:
        form = row ^ 1
        monomials = [0] if form & 1 else []
        mask = form >> 1
        while mask:
            bit = mask & -mask
            monomials.append(bit)
            mask ^= bit
        new = set()
        for left in terms:
            for right in monomials:
                new.symmetric_difference_update((left | right,))
        terms = new
    return terms


def retain(charts):
    basis = {}
    retained = []
    for chart in charts:
        equations = normal(chart.equations)
        if equations is None:
            continue
        row = indicator(equations)
        while row:
            pivot = max(row)
            if pivot not in basis:
                basis[pivot] = row
                retained.append(Chart(equations, chart.witness))
                break
            row ^= basis[pivot]
    return retained


def substitute(form, bit, value):
    return (form ^ bit ^ value) if form & bit else form


def eliminate(chart, bit, guard):
    pivot = next((row for row in chart.equations if row & bit), None)
    if pivot is None:
        witness = tuple(substitute(f, bit, 0) for f in chart.witness)
        yield Chart(chart.equations, (0,) + witness)
        return
    value = pivot ^ bit
    base = tuple(substitute(row, bit, value) for row in chart.equations if row != pivot)
    witness = (value,) + tuple(substitute(f, bit, value) for f in chart.witness)
    yield Chart(base + (value,), witness)
    for literal in guard:
        yield Chart(base + (substitute(literal, bit, 1) ^ 1,), witness)


def compile_charts(observed, guards, terminal):
    charts = [Chart(())]
    for clause in terminal:
        charts = retain(Chart(c.equations + (literal ^ 1,)) for c in charts for literal in clause)
    for j in reversed(range(len(guards))):
        bit = 1 << (observed + j + 1)
        charts = retain(child for c in charts for child in eliminate(c, bit, guards[j]))
    return charts
