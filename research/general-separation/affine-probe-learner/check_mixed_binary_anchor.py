"""Independent original-word and literal-occurrence controls."""
from itertools import product
from random import Random

from mixed_binary_anchor import solve


def bit(n,x,i):
    return (x >> (n-1-i)) & 1


def valid(n,x,clauses,rows):
    return (all(any(bit(n,x,i) == b for i,b in clause) for clause in clauses)
            and all((x & mask).bit_count() % 2 == b for mask,b in rows))


def compare(n,clauses,rows):
    words = {x for x in range(1 << n) if valid(n,x,clauses,rows)}
    result = solve(n,clauses,rows)
    assert (result.witness is None) == (not words)
    if words:
        assert result.witness in words
    if result.route != 'inconsistent':
        assert result.route == ('coordinate' if result.p <= result.q else 'affine')
        assert 1 <= result.fibers <= 1 << min(result.p,result.q)
        if not words:
            assert result.fibers == 1 << min(result.p,result.q)
    return result


def anchors():
    assert compare(0,[],[]).witness == 0
    assert compare(0,[()],[]).witness is None
    assert compare(0,[],[(0,1)]).witness is None
    assert compare(3,[],[(3,0),(3,1)]).route == 'inconsistent'
    assert compare(3,[((0,0),),((0,1),)],[]).witness is None
    # Separately feasible caches, incompatible together.
    assert compare(3,[((0,0),),((1,0),)],[(6,1)]).witness is None
    assert (compare(4,[((i,1),) for i in range(4)],[(15,0)]).p,
            compare(4,[((i,1),) for i in range(4)],[(15,0)]).q) == (2,0)
    strict = compare(4,[((0,1),(1,1)),((2,0),(3,0))],[])
    assert (strict.p,strict.q) == (0,2)
    # All three active coordinates are pinned, private final bit equals parity.
    # The sole long row projects away; its private bit is uniquely recovered.
    private = compare(4,[((0,1),),((1,0),),((2,0),)],[(15,0)])
    assert private.witness == 9 and private.p == 0
    # Two long rows sharing one private coordinate leave an actual active check.
    compare(5,[((0,1),),((1,1),(2,1)),((3,1),)],[(0b11101,1),(0b10011,0)])
    rng = Random(19241)
    for n in range(1,6):
        for _ in range(25):
            row = [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(5))]
            cnf = [tuple((rng.randrange(n),rng.randrange(2)) for _ in range(rng.randrange(1,3)))
                   for _ in range(rng.randrange(7))]
            compare(n,cnf,row)


def gadget(original):
    # Signed DIMACS literals; one physical copy per literal occurrence.
    expanded,groups = [],{}
    copies = 0
    for clause in original:
        terms = []
        for lit in clause:
            groups.setdefault(abs(lit),[]).append(copies)
            terms.append((copies,int(lit > 0)))
            copies += 1
        expanded.append(terms)
    for indices in groups.values():
        if len(indices) > 1:
            for l,r in zip(indices,indices[1:]+indices[:1]):
                expanded.append([(l,0),(r,1)])
    n = copies + sum(map(len,expanded))
    shift = copies
    cnf,rows = [],[]
    degree = [0]*copies
    for clause in expanded:
        mask = 0
        for i,b in clause:
            cnf.append(((shift,0),(i,b)))
            degree[i] += 1
            mask |= 1 << (n-1-shift)
            shift += 1
        rows.append((mask,1))
    assert max(degree,default=0) <= 3 and shift == n
    assert all(a.bit_count() in (2,3) for a,_ in rows)
    assert sum(a.bit_count() for a,_ in rows) == n-copies
    assert sum(a for a,_ in rows) == (1 << (n-copies))-1
    assert valid(n,0,cnf,[])
    # All original copy assignments, with exact elimination of private
    # selectors by truth enumeration on each row independently.
    by_original = set()
    for assignment in range(1 << copies):
        ways = 1
        for clause in expanded:
            allowed = [bit(copies,assignment,i) == b for i,b in clause]
            ways *= sum(sum(s)%2 == 1 and all(not v or ok for v,ok in zip(s,allowed))
                        for s in product((0,1),repeat=len(clause)))
        if ways:
            assert all(len({bit(copies,assignment,i) for i in ids}) == 1 for ids in groups.values())
            by_original.add(tuple(bit(copies,assignment,groups[i][0]) for i in sorted(groups)))
    def satisfies(word):
        env = dict(zip(sorted(groups),word))
        return all(any(env[abs(lit)] == (lit>0) for lit in clause) for clause in original)
    assert by_original == {w for w in product((0,1),repeat=len(groups)) if satisfies(w)}
    result = solve(n,cnf,rows)
    assert (result.witness is None) == (not by_original)
    if by_original:
        assert valid(n,result.witness,cnf,rows)
        decoded = tuple(bit(n,result.witness,groups[i][0]) for i in sorted(groups))
        assert decoded in by_original


if __name__ == '__main__':
    anchors()
    gadget([(1,1,-2),(-1,2,2)])
    gadget([(1,1,1),(-1,-1,-1)])
    print('Original mixed anchors and occurrence/selector reductions agree.')
