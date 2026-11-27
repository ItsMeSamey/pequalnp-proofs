from one_defect_uniform_tournament import search
from random import Random
from itertools import combinations


def tournament(n,code):
    rows=[1<<i for i in range(n)]
    for k,(i,j) in enumerate(combinations(range(n),2)):
        if code>>k&1:
            rows[j]|=1<<i
        else:
            rows[i]|=1<<j
    return rows


def verify(rows,b,good):
    w=search(rows,b)
    assert (w is not None)==any((x&b).bit_count()%2 for x in good)
    if w:
        z=sum(1<<i for i in w)
        assert len(set(w))==len(w) and len(w) in (3,4) and z in good and (z&b).bit_count()%2


def supports(rows):
    return [z for z in range(1,1<<len(rows)) if all(not(z>>i&1 and (z&r).bit_count()%2) for i,r in enumerate(rows))]


if __name__=='__main__':
    total=0
    for n in range(1,6):
        for c in range(1<<(n*(n-1)//2)):
            rows=tournament(n,c)
            good=supports(rows)
            for b in range(1<<n):
                verify(rows,b,good)
                total+=1
    rng=Random(387)
    for _ in range(300):
        n=rng.randrange(6,12)
        rows=tournament(n,rng.getrandbits(n*(n-1)//2))
        b=rng.randrange(1<<n)
        verify(rows,b,supports(rows))
        mask=rng.randrange(1<<n)
        changed=[r^((mask&(1<<i))) for i,r in enumerate(rows)]
        assert search(changed,b,offset=mask)==search(rows,b)
    for offset in (1,7):
        try:
            search(tournament(3,2),7,offset=offset)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid effective parity accepted')
    print(total,'exhaustive tournament/mark cases, 300 random raw and offset controls, parity rejections passed')
