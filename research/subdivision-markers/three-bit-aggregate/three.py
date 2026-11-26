"""Exact three-bit aggregate selector on an arbitrary represented binary matroid."""
from itertools import combinations
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[1] / "unseeded-root-states"))
from solve import eliminate, image, solve


def basis(cols, order):
    pivots = {}
    chosen = []
    for i in order:
        v = cols[i]
        while v:
            bit = v.bit_length()-1
            if bit not in pivots:
                pivots[bit] = v
                chosen.append(i)
                break
            v ^= pivots[bit]
    return chosen


def points(matrix):
    a, b = matrix
    return a, b, a^b


def on_basis(cols, tags, tree):
    tree = set(tree)
    ordinary = [i for i in range(len(cols)) if i in tree]
    tree_cols = [cols[i] for i in ordinary]
    circuits, gains = [], []
    states = {0: (0, 0)}
    for e in range(len(cols)):
        if e in tree:
            continue
        path = solve(tree_cols, cols[e])
        assert path is not None
        c = (1<<e) | sum(1<<i for j,i in enumerate(ordinary) if path>>j & 1)
        circuits.append(c)
        gain = tuple(image(axis,c) for axis in zip(*tags))
        gains.append(gain)
        nxt = {}
        for s,(f,g) in states.items():
            for v,delta in enumerate(points(gain),1):
                nxt.setdefault(s^delta, (f^(c if v&1 else 0), g^(c if v&2 else 0)))
        states = nxt
    return circuits, gains, states


def select(cols, tags, target):
    """Return (f,g) as bit masks and the decision branch that supplied them."""
    cols, tags = tuple(cols), tuple(tags)
    if len(cols)!=len(tags) or not 0<=target<8 or any(len(t)!=2 or any(not 0<=x<8 for x in t) for t in tags):
        raise ValueError("one two-column, three-bit linear tag per ordinary element is required")
    ground = list(range(len(cols)))
    cs, gs, answers = on_basis(cols,tags,basis(cols,ground))
    if target in answers:
        return answers[target], "reference"
    if solve([v for M in gs for v in M],target) is None:
        return None, "outside image"
    punctured = [j for j,M in enumerate(gs) if 0 not in points(M)]
    dual = [sum(((c>>e)&1)<<j for j,c in enumerate(cs)) for e in ground]

    def trial(cotree):
        _,_,found = on_basis(cols,tags,set(ground)-set(cotree))
        return found.get(target)

    if len(punctured)==1:
        ell = 1 << punctured[0]
        choices = [e for e in ground if dual[e]!=ell]
        coeff = solve([dual[e] for e in choices],ell)
        if coeff is None:
            return None, "one forced"
        used = [e for i,e in enumerate(choices) if coeff>>i & 1]
        found = trial(basis(dual,used+ground))
        assert found is not None
        return found, "one spread"

    assert len(punctured)==2 and sum(M!=(0,0) for M in gs)==2
    ell, eta = (1<<i for i in punctured)
    flat = {0,ell,eta,ell^eta}
    outer = [e for e in ground if dual[e] not in flat]
    cotree = basis(dual,outer+ground)
    if sum(dual[e] in flat for e in cotree)<2:
        found = trial(cotree)
        assert found is not None
        return found, "two spread"
    inside = {dual[e]:e for e in ground if dual[e] in flat and dual[e]}
    for pair in combinations(inside.values(),2):
        found = trial(basis(dual,[*pair,*outer]))
        if found is not None:
            return found, "two split yes"
    return None, "two split no"
