"""Compare individual 2SAT branches against all original raw words."""
from itertools import product
from unittest.mock import patch
import shared_entry_cover as backend


def verify(n, gates, pins, canonical, original, expected):
    def trace(raw):
        w = list(raw)
        for a,b in gates:
            w.append(int(not(w[a] and w[b])))
        return w
    def accepts(w):
        return all(w[i]==v for i,v in pins)
    assignments = list(product((0,1),repeat=len(canonical)))
    possible = set()
    for raw in product((0,1),repeat=n):
        w = trace(raw)
        if accepts(w):
            possible.add(tuple(w[i] for i in original))
    vector = [a in possible for a in assignments]
    assert vector == expected
    answers = []
    original_sat = backend._sat
    def record(nbits, rows):
        answers.append(original_sat(nbits,rows) is not None)
        # Continue after successes to observe every branch of this model.
        return None
    with patch.object(backend, '_sat', record):
        _,cover,_,_ = backend.solve(n,gates,pins=pins)
    assert cover == canonical and answers == vector
    status,actual,_,raw = backend.solve(n,gates,pins=pins)
    assert actual == canonical and status == ('sat' if any(vector) else 'unsat')
    if raw is None:
        assert not any(vector)
    else:
        w = trace(raw)
        assert len(raw)==n and accepts(w)
        assert tuple(w[i] for i in original) == assignments[vector.index(True)]
    return answers


def main():
    # One visible word has both preimages under the private primary.
    a = verify(2,[(1,0),(1,2)],[(1,0),(2,1),(3,1)],(0,),(0,),[True,True])
    # x,h,a,b,c,d,e as raw bits. y=NAND(~a,b), original 10/canonical 9.
    # The final tapped gate is the complement of y.
    gates = [(1,0),(1,7),(2,2),(9,3),(10,4),(10,5),(10,6),(10,10)]
    pins = [(1,1),(7,0),(8,1),(4,1),(5,1),(6,1),
            (11,1),(12,1),(13,1),(14,1)]
    b = verify(7,gates,pins,(0,9),(0,10),[False,False,True,False])
    c = verify(7,gates,pins+[(2,1)],(0,9),(0,10),[False]*4)
    print([a,b,c])


if __name__ == '__main__':
    main()
