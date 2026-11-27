"""Independent physical OR-DAG search on capped banks, allowing unrestricted fanout."""
from itertools import combinations
from random import Random
from h5_terminal_prefix import finish


def dag_pairs(m, depth):
    # Index each wire by its FORMAL set of bank leaves; different leaves remain
    # distinct even when they compute identical truth values. Wire zero is free.
    seed = frozenset([0, *(1 << i for i in range(m))])
    frontier = {seed}
    seen = set(frontier)
    pairs = {}
    for gates in range(depth + 1):
        new = set()
        for wires in frontier:
            for a in wires:
                for b in wires:
                    if a <= b:
                        pairs.setdefault((a, b), gates)
                    if a >= b or gates == depth:
                        continue
                    c = a | b
                    if c in wires:
                        continue  # aliases and repetitions are free to reuse
                    state = wires | {c}
                    if state not in seen:
                        new.add(state)
        seen.update(new)
        frontier = new
        if not frontier:
            break
    return pairs


def search(bank, full_pos, hidden, dag):
    unions = {0:(0, 0, False)}
    for i, (p, n) in enumerate(bank):
        unions.update({s | 1<<i: (sp|p, sn|n, sh or bool(hidden and hidden[i]))
                       for s,(sp,sn,sh) in list(unions.items())})
    return min((cost for (a,b), cost in dag.items()
                if unions[a][0] == unions[b][0] == full_pos
                and not unions[a][1] & unions[b][1]
                and (hidden is None or unions[a][2] and unions[b][2])), default=None)


def compare(bank, np, nn, flags, dag, depth):
    oracle = search(bank, (1<<np)-1, flags, dag)
    result = finish(bank, np, nn, flags)
    got = result[0] if result is not None else None
    assert oracle == (got if got is not None and got <= depth else None), (oracle, result)
    if result is not None:
        _, left, right = result
        masks = []
        for arm in (left, right):
            p = n = 0
            for i in arm:
                pi, ni = bank[i]
                p |= pi
                n |= ni
            assert p == (1<<np)-1 and (flags is None or any(flags[i] for i in arm))
            masks.append(n)
        assert not masks[0] & masks[1]
    return got


def physical_bank(n, prefix, target):
    xs = list(range(1<<n))
    labels = [[(x>>i)&1 for x in xs] for i in range(n)]
    flags = [False]*n
    for gate, i, j in prefix:
        if gate == 'zero':
            labels.append([0]*len(xs)); flags.append(False)
        elif gate == 'or':
            labels.append([a|b for a,b in zip(labels[i],labels[j])])
            flags.append(flags[i] or flags[j])
        else:
            assert gate == 'and'
            labels.append([a&b for a,b in zip(labels[i],labels[j])]); flags.append(True)
    pos = [x for x in xs if target(x) and all(not target(x ^ 1<<i) for i in range(n) if x>>i&1)]
    neg = [x for x in xs if not target(x) and all(target(x | 1<<i) for i in range(n) if not x>>i&1)]
    bank = []
    active_flags = []
    for row, hidden in zip(labels, flags):
        if not any(row):
            continue
        p = sum(row[x]<<i for i,x in enumerate(pos))
        nmask = sum(row[x]<<i for i,x in enumerate(neg))
        assert nmask
        bank.append((p,nmask)); active_flags.append(hidden)
    return bank,len(pos),len(neg),active_flags


def check():
    dag = dag_pairs(4, 11)  # exhaust all 11 nontrivial formal OR functions
    assert len(dag) == 16*17//2
    assert dag[7,11] == 3  # (a|b)|c and (a|b)|d reuse the INTERNAL a|b
    rng = Random(91553)
    results = [0,0]
    for i in range(280):
        p = rng.randrange(1,4); n = rng.randrange(1,4)
        bank = [(rng.randrange(1<<p),rng.randrange(1,1<<n)) for _ in range(4)]
        flags = [bool(rng.randrange(2)) for _ in bank] if i%2 else None
        value = compare(bank,p,n,flags,dag,11)
        results[value is not None] += 1

    # A leaky hidden label on either arm covers NO minimal positive. Retain it
    # solely for the syntactic hidden-source requirement. Source z and OR with
    # zero are available in the physical description and fold as usual.
    bank,p,n,flags = physical_bank(3,[('and',0,2),('and',1,2),('zero',0,0)],
                                  lambda x:x & 3 == 3)
    assert all(not bank[i][0] for i in (3,4))
    dag5 = dag_pairs(5,2)
    assert compare(bank,p,n,None,dag5,2) == 0
    assert compare(bank,p,n,flags,dag5,2) == 2
    # With only one marked leaky label, both arms cannot contain a hidden
    # primitive: the negative on which it leaks would activate both arms.
    assert compare(bank,p,n,[False,False,False,True,False],dag5,2) is None
    # Formal zero may be omitted, but the leaky-bank API must reject a
    # caller that passes it directly.
    try:
        finish([*bank,(0,0)],p,n)
    except ValueError:
        pass
    else:
        raise AssertionError('zero wire supplied as a leaky bank atom')

    # A precharged shared OR is an operand of BOTH earlier ANDs. Their distinct
    # outputs are both leaky. The target accepts their product directly.
    bank,p,n,flags = physical_bank(4,[('or',0,1),('and',4,2),('and',4,3)],
                                  lambda x:bool(x&3) and x&12==12)
    assert compare(bank,p,n,flags,dag_pairs(7,0),0) == 0

    # A precharged OR carrying a hidden primitive is itself usable on the arm.
    bank,p,n,flags = physical_bank(3,[('and',0,2),('and',1,2),('or',0,3),('or',1,4)],
                                  lambda x:x & 3 == 3)
    assert flags[-2:] == [True,True]
    assert compare(bank,p,n,flags,dag_pairs(7,0),0) == 0
    print('280 complete four-leaf DAG comparisons (NO,YES)',results,
          '; shared-gate, hidden-zero-positive, zero-wire and precharged prefix fixtures passed')


if __name__ == '__main__':
    check()
