"""Exact existential projection of sparse signed CNF through <=2 boundary bits.

project returns a Kernel with residual clauses and reverse witness sections.
Unused source IDs default false. A viable residual assignment may also name
irrelevant original bits; bits of eliminated variables are set by the sections.
A successful step preserves existence, not solution multiplicities.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import combinations
from ring_image_group_horn_strict import _rename


def _normalize(rows):
    unique = {frozenset(row) for row in rows}
    clean = sorted((r for r in unique if not any(-x in r for x in r)),
                   key=lambda r: (len(r), tuple(sorted(r))))
    kept = []
    for row in clean:
        if not any(r <= row for r in kept):
            kept.append(row)
    return tuple(kept)


def _satisfies(rows, true):
    return all(any((abs(x) in true) == (x > 0) for x in row) for row in rows)


def _binary(rows):
    if any(not row for row in rows):
        return None
    pairs = []
    labels = set()
    for row in rows:
        pair = tuple(sorted(row))
        if len(pair) > 2:
            raise ValueError("expected a binary clause")
        pairs.append(pair if len(pair) == 2 else pair*2)
        labels.update(map(abs, pair))
    # On pairs the shared SCC routine implements the two clause implications.
    model = _rename(sorted(labels), pairs)
    if model is not None and not _satisfies(rows, model):
        raise AssertionError("invalid local 2-SAT model")
    return model


@dataclass(frozen=True)
class Step:
    private: tuple
    boundary: tuple
    witnesses: dict  # boundary bit mask -> tuple of true private IDs
    kind: str


@dataclass(frozen=True)
class Kernel:
    arity: int
    original: tuple
    residual: tuple
    steps: tuple

    def lift(self, true_ids):
        truth = set()
        for v in true_ids:
            if type(v) is not int or not 1 <= v <= self.arity:
                raise ValueError("invalid source variable ID")
            truth.add(v)
        if not _satisfies(self.residual, truth):
            raise ValueError("assignment does not satisfy residual")
        for step in reversed(self.steps):
            mask = sum(1 << j for j,v in enumerate(step.boundary) if v in truth)
            witness = step.witnesses.get(mask)
            if witness is None:
                raise AssertionError("missing section for a viable boundary")
            truth.difference_update(step.private)
            truth.update(witness)
        if not _satisfies(self.original, truth):
            raise AssertionError("invalid original witness")
        return tuple(sorted(truth))


def _graph(rows):
    graph = {}
    for row in rows:
        names = set(map(abs, row))
        for v in names:
            graph.setdefault(v, set()).update(names - {v})
    return graph


def _triples(graph, occurrence):
    unseen = {v for v in graph if occurrence[v] == 4}
    for root in sorted(unseen):
        if root not in unseen:
            continue
        unseen.remove(root)
        comp, pending = {root}, [root]
        while pending:
            new = graph[pending.pop()] & unseen
            comp.update(new)
            pending.extend(new)
            unseen.difference_update(new)
        if len(comp) == 3 and len(set().union(*(graph[v] for v in comp)) - comp) == 2:
            yield comp


def _pieces(graph):
    vertices = tuple(sorted(graph))
    for size in range(3):
        for cut in combinations(vertices, size):
            unseen = set(vertices).difference(cut)
            for root in vertices:
                if root not in unseen:
                    continue
                unseen.remove(root)
                comp, pending = {root}, [root]
                while pending:
                    here = pending.pop()
                    new = graph[here] & unseen
                    pending.extend(new)
                    comp.update(new)
                    unseen.difference_update(new)
                yield comp


def _try(rows, private, kind):
    touched, outside, boundary = [], [], set()
    for row in rows:
        names = set(map(abs, row))
        if names & private:
            touched.append(row)
            boundary.update(names-private)
        else:
            outside.append(row)
    if not touched or len(boundary)>2:
        return None
    if not private <= {abs(x) for row in touched for x in row}:
        return None
    if kind == "private_triple" and (len(boundary)!=2 or len(touched)!=6 or
            any(len(row)!=3 or len(set(map(abs,row)) & private)!=2 for row in touched)):
        return None
    boundary = tuple(sorted(boundary))
    witnesses, forbidden = {}, []
    for mask in range(1 << len(boundary)):
        pinned = {(v if mask & (1 << j) else -v) for j,v in enumerate(boundary)}
        local = [r - {-x for x in pinned} for r in touched if not r & pinned]
        if any(len(row)>2 for row in local):
            return None
        model = _binary(local)
        if model is None:
            forbidden.append(tuple(-x for x in pinned))
        else:
            witnesses[mask] = tuple(sorted(model))
    step = Step(tuple(sorted(private)), boundary, witnesses, kind)
    return _normalize([*outside,*forbidden]), step


def project(arity, signed_clauses):
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    original = tuple(tuple(row) for row in signed_clauses)
    if any(type(x) is not int or not 1 <= abs(x) <= arity for r in original for x in r):
        raise ValueError("invalid signed source literal")
    occurrences = Counter(abs(x) for r in original for x in r)
    rows = _normalize(original)
    steps = []
    # Initial physical counts survive renaming and changes of signs. Determine
    # all candidates before projecting any gadget. Recheck each current piece.
    for private in _triples(_graph(rows), occurrences):
        result = _try(rows, private, "private_triple")
        if result is not None:
            rows, step = result
            steps.append(step)
    while rows and all(rows):
        graph = _graph(rows)
        for private in _pieces(graph):
            result = _try(rows, private, "separator")
            if result is not None:
                rows, step = result
                steps.append(step)
                break
        else:
            break
    return Kernel(arity, original, tuple(tuple(sorted(r)) for r in rows), tuple(steps))


def solve_source_sparse(arity, signed_clauses):
    kernel = project(arity, signed_clauses)
    rows = kernel.residual
    if any(len(r)>2 for r in rows):
        return dict(status="unknown", reason="residual_width", residual=rows)
    model = _binary(rows)
    if model is None:
        return dict(status="zero")
    return dict(status="nonzero", true_ids=kernel.lift(model))
