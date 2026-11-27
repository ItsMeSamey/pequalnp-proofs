"""04-only exhaustive check of projected endpoint words and physical extensions."""
from itertools import product
from random import Random

from path_kernel import path_kernel


def holds(bits, clauses):
    return all(any(bits[x] ^ bits[y] == d for x,y,d in clause) for clause in clauses)


def audit(n, clauses):
    kernel = path_kernel(n, clauses)
    endpoints = kernel.endpoints
    assert len(set(endpoints)) == len(endpoints)
    assert all(x in endpoints and y in endpoints
               for clause in kernel.clauses for x,y,_ in clause)
    feasible = {tuple(full[j] for j in endpoints)
                for full in product((0,1), repeat=n) if holds(full, clauses)}
    for word in product((0,1), repeat=len(endpoints)):
        assigned = dict(zip(endpoints,word))
        expected = word in feasible
        assert holds(assigned, kernel.clauses) == expected
        for pins in (assigned, tuple(assigned.get(i,0) for i in range(n))):
            lifted = kernel.lift(pins)
            assert (lifted is not None) == expected
            if lifted is not None:
                assert len(lifted) == n and all(b in (0,1) for b in lifted)
                assert holds(lifted,clauses) and tuple(lifted[j] for j in endpoints) == word
    return kernel, len(feasible)


def signed_copies():
    # The API takes contracted comparisons. Here the original clauses and signed
    # copies are checked independently; expansion into original bits is test code.
    pins = [(0,3,1),(1,5,0),(2,6,1),(4,7,1)]
    names = (0,1,2,0,3,1,2,3)
    offset = (0,0,0,1,0,0,1,1)
    original = [[(0,4,1),(3,6,1),(2,7,0)],[(3,5,1)],[(0,1,0),(5,7,1)]]
    contracted = [[(names[x],names[y],d^offset[x]^offset[y]) for x,y,d in clause]
                  for clause in original]
    kernel,_ = audit(4,contracted)
    def original_ok(bits):
        return holds(bits,original) and all(bits[x]^bits[y]==s for x,y,s in pins)
    source = {tuple(bits[j] for j in (0,1,2,4)) for bits in product((0,1),repeat=8)
              if original_ok(bits)}
    for word in product((0,1),repeat=len(kernel.endpoints)):
        given=dict(zip(kernel.endpoints,word))
        possible=any(all(x[j]==b for j,b in given.items()) for x in source)
        lifted=kernel.lift(given)
        assert (lifted is not None)==possible
        if lifted is not None:
            physical=tuple(lifted[j]^s for j,s in zip(names,offset))
            assert original_ok(physical)


def main():
    assert audit(0,[])[1]==1
    assert audit(0,[[]])[1]==0
    assert audit(1,[[(0,0,1)]])[1]==0
    for clauses in (
        [[(0,0,1),(0,0,0)],[(1,1,0)]],
        [[(0,1,0)],[(0,1,1)]],
        [[(0,1,1),(1,2,0),(2,0,0)]],
        [[(0,1,0),(1,2,0)],[(2,3,1),(3,0,0)]],
        [[(0,1,1)]*4,[(0,1,0)]*3],
        [[(0,1,0),(1,2,0),(2,3,0)],[(3,0,1)]],
    ):
        audit(4,clauses)

    # Five independent paths (degrees 1,2,2,2,1 in the resource tree)
    # give one projected clause of arity five. Mark every end pair opposite
    # to see a NO conditional input, even though the unconstrained input is YES.
    ps=[[(0,1,0)],[(2,3,0),(3,4,0)],[(5,6,0),(6,7,0)],
        [(8,9,0),(9,10,0)],[(11,12,0)]]
    kernel,good=audit(13,[[p[-1],q[0]] for p,q in zip(ps,ps[1:])])
    assert [len(clause) for clause in kernel.clauses]==[5] and good==4**5-2**5

    signed_copies()
    rng=Random(96411)
    for _ in range(100):
        n=rng.randrange(1,7)
        clauses=[[(rng.randrange(n),rng.randrange(n),rng.randrange(2))
                  for _ in range(rng.randrange(6))] for _ in range(rng.randrange(6))]
        audit(n,clauses)
    print('111 graph fixtures including signed original-copy replay; all endpoint words checked')


if __name__=='__main__':
    main()
