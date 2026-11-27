"""Original-word controls for joint clauses and affine repairs."""
from binary_fault_retraction import Gamma
from check_binary_fault_solver import Source, codewords, raw, simplex
from joint_fault_retraction import affine_conjuncts, compile_joint_retraction
from joint_fault_solver import solve


def accepts(n, clauses, rows, x):
    return (all(any(((x >> (n-1-i)) & 1) == b for i,b in c) for c in clauses)
            and all((x & mask).bit_count()%2 == b for mask,b in rows))


def check(n,F):
    original = {x for x in range(1 << n) if raw(n,F,x)}
    got = solve(n,F)
    assert (got['status'] == 'witness') == bool(original)
    if original:
        assert got['assignment'] in original
    assert all(accepts(n,got['clauses'],got['rows'],x) for x in original)
    assert got['fresh_rows'] == len(set(got['rows']))
    assert got['fresh_clauses'] == len(set(got['clauses']))
    assert got['anchor_calls'] == got['phases'] + (got['reason'] == 'mixed_inconsistent')
    return original,got


def mixed():
    c = Source(2)
    # NAND(x,true) is an opaque, distinct-parent node. Both gated copies
    # point at the same mixed conjunction; the raw predicate is identically 0.
    veto = c.nand(0,-2)
    sub = c.both(0,veto)
    F = c.finish(c.both(sub,sub))
    assert affine_conjuncts(2,*F) == ((2,1),)
    words,got = check(2,F)
    assert not words and got['reason'] == 'mixed_inconsistent'
    assert got['fresh_rows'] == got['fresh_clauses'] == 1
    assert all(any(accepts(2,clauses,rows,x) for x in range(4))
               for clauses,rows in ((got['clauses'],()),((),got['rows'])))
    assert not any(accepts(2,got['clauses'],got['rows'],x) for x in range(4))


def projection():
    n = 4
    c = Source(n)
    w = c.xor(0,3)
    F = c.finish(c.both(c.nand(w,1),c.nand(w,2)))
    gamma = Gamma(n)
    gamma.add_cube(((0,1),(1,0)))
    rows = ((0b1101,1),(0b0110,0))
    allowed = {x for x in range(16) if accepts(n,gamma.clauses,rows,x)}
    assert 1 < len(allowed) < 16
    for anchor in range(16):
        if anchor not in allowed:
            try:
                compile_joint_retraction(n,*F,gamma,rows,anchor)
            except ValueError:
                continue
            raise AssertionError('bad anchor accepted')
        compiled = compile_joint_retraction(n,*F,gamma,rows,anchor)
        for x in range(16):
            target = x if x in allowed else anchor
            assert compiled.accepts(x) == (x in allowed)
            assert compiled.lift(x) == target
            assert raw(n,(compiled.gates,compiled.output),x) == raw(n,F,target)


def main():
    for out in (-1,-2):
        check(0,((),out))
    mixed()
    projection()
    # Identify the code by its systematic message, independently of the solver.
    F = simplex()
    native = {x for x in range(128) if raw(7,F,x)}
    rows = affine_conjuncts(7,*F)
    assert len(rows) == 4 and native == codewords()
    assert {x for x in range(128) if accepts(7,(),rows,x)} == native
    words,got = check(7,F)
    assert words == native and got['k'] == got['fresh_clauses'] == 0
    assert 1 <= got['fresh_rows'] <= 4
    def never(*args):
        raise AssertionError('custom learner called before bound validation')
    try:
        solve(1,((),0),learner_factory=never)
    except ValueError:
        pass
    else:
        raise AssertionError('missing custom bound accepted')


if __name__ == '__main__':
    main()
    print('Joint restart, lift and original-word controls passed.')
