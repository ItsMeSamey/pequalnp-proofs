"""Direct enumeration of Boolean affine charts on named coordinate blocks."""
from itertools import combinations, product
from read_two_ring_nonzero import compile_nonzero
from ring_image_block_horn import solve_source_sparse,solve_sparse,_centers


def candidates(d,points,raw_only=False):
    for cols in combinations(range(1,1<<d),d):
        if raw_only and set(cols)!={1<<i for i in range(d)}:
            continue
        lut=[sum(1<<j for j,a in enumerate(cols) if (x&a).bit_count()%2)
             for x in range(1<<d)]
        if len(set(lut))!=len(lut):
            continue
        # Row permutations preserve every Hamming weight, so ordered
        # variants of a basis impose the same Horn checks.
        for origin in range(1<<d):
            if all(lut[x^origin].bit_count()<=1 for x in points):
                yield cols,origin


def point_clause(ids,word):
    return tuple(-i if word>>j&1 else i for j,i in enumerate(ids))


def check(n,rows,want,physical=False):
    if physical:
        raw=compile_nonzero(n,rows)
        result=solve_sparse(*(raw[k] for k in ('n','clauses','point','k')))
    else:
        result=solve_source_sparse(n,rows)
    assert result['status']==want,(rows,result,want)
    if want=='nonzero':
        selected=set(result['true_ids'])
        assert all(any((abs(i) in selected)==(i>0) for i in row) for row in rows)
    return result


def main():
    for d in (2,3):
        block=tuple(range(1,d+1))
        for mask in range(1,1<<(1<<d)):
            points=[w for w in range(1<<d) if mask>>w&1]
            possible=any(origin in points for _,origin in candidates(d,points))
            charts,reason=_centers([{1:w} for w in points],{1:list(range(1,d+1))})
            assert (reason is None)==possible
        for words in combinations(range(1<<d),2):
            # The fresh last coordinate distinguishes the second logical group.
            # Both block points, together with their private-coordinate choices,
            # can be tested without access to the producer's common basis.
            rows=[point_clause(block,words[0]),point_clause(block+(d+1,),words[1])]
            assert any(candidates(d,words))
            check(d+1,rows,'nonzero')
        if d==3:
            assert not any(candidates(d,(0,7),True))
            assert any(candidates(d,(0,7)))
            check(4,[point_clause(block,0),point_clause(block+(4,),7)],'nonzero',True)
    # Four separate groups force incompatible center choices on x and y.
    # The two singleton groups distinguish their incidence signatures. Extra
    # private dimensions cannot repair two simultaneous mismatches on x,y.
    rows=[(1,7),(2,8)]+[point_clause((1,2,3+w),w) for w in range(4)]
    assert not any(all(((w^z)&3).bit_count()<=1 for w in range(4)) for z in range(4))
    assert check(8,rows,'unknown',True)['reason']=='no_block_centers'
    check(1,[(1,),(-1,)],'zero',True)
    huge=1<<300
    check(huge,[(huge,),(-huge,1)],'nonzero')
    print('Block bases/origins, physical center conflict and sparse witnesses passed.')


if __name__=='__main__':
    main()
