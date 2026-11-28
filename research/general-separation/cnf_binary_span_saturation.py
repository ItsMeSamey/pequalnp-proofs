"""Derive empty/unary/binary clauses from the GF(2) span of residual misses.

A membership-only query appends a ternary padded with fresh variables fixed
false. All candidates in one batch are tested on the same old background.
Nonzero accepted functions vanish on the new background, so a nonempty round
strictly drops the residual rank. Discovery streams O((1+h)**2) candidates
per scan for h named inputs, does polynomial work per candidate, and takes at
most initial rank+1 scans. Numeric arity is used only for validation and
computing three fresh labels. The terminal budgets govern their own stages.
"""
from dataclasses import dataclass
from itertools import combinations, product

import cnf_binary_background_rank as rank_engine


@dataclass(frozen=True)
class Saturation:
    arity: int
    original: tuple
    used: tuple
    derived: tuple
    rounds: tuple
    ranks: tuple
    basis: rank_engine.BackgroundBasis


def _candidates(names):
    yield ()
    for v in names:
        yield (v,)
        yield (-v,)
    for a,b in combinations(names,2):
        for s,t in product((1,-1), repeat=2):
            yield tuple(sorted((s*a,t*b)))


def project(arity,clauses):
    initial = rank_engine.project(arity,clauses)
    original = initial.original
    basis, rounds, derived = initial, [], []
    ranks = [initial.rank]
    fresh = tuple(arity+j for j in (1,2,3))
    pins = tuple((-j,) for j in fresh)
    while basis.feasible and basis.rank:
        current = original + tuple(derived)
        padded = current + pins
        padded_rank = rank_engine.project(arity+3,padded).rank
        if padded_rank != basis.rank:
            raise AssertionError("fixed fresh variables changed the residual rank")
        present = set(basis.background)
        batch = []
        for candidate in _candidates(initial.used):
            if candidate in present:
                continue
            # A zero miss would leave the span dimension unchanged vacuously.
            if candidate and rank_engine._model(basis.background,tuple(-x for x in candidate)) is None:
                continue
            test = candidate + fresh[:3-len(candidate)]
            if rank_engine.project(arity+3, padded+(test,)).rank == padded_rank:
                batch.append(candidate)
                if not candidate:
                    break
        if not batch:
            break
        rounds.append(tuple(batch))
        derived.extend(batch)
        basis = rank_engine.project(arity,original+tuple(derived))
        if basis.rank >= ranks[-1]:
            raise AssertionError("nonempty batch failed to drop residual rank")
        ranks.append(basis.rank)
    return Saturation(arity, original, initial.used, tuple(derived), tuple(rounds), tuple(ranks), basis)


def _metadata(out, saturation):
    out.update(saturation_rounds=len(saturation.rounds), rank_history=saturation.ranks,
               derived=saturation.derived)
    return out


def solve(arity,clauses,*,max_branches=None):
    if max_branches is not None and (type(max_branches) is not int or max_branches<0):
        raise ValueError("invalid branch cap")
    sat = project(arity,clauses)
    answer = rank_engine.solve(arity,sat.original+sat.derived,max_branches=max_branches)
    return _metadata(answer,sat)


def count(arity,clauses,*,max_terms=None):
    import cnf_binary_background_count as counter
    if max_terms is not None and (type(max_terms) is not int or max_terms<0):
        raise ValueError("invalid count cap")
    sat = project(arity,clauses)
    answer = counter.count(arity,sat.original+sat.derived,max_terms=max_terms)
    return _metadata(answer,sat)
