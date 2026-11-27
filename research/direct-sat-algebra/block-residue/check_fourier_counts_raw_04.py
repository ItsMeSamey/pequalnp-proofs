"""04-only exact count and original witness comparisons, including gauge bits."""
from itertools import product
from random import Random
from syndrome_fourier import fourier_count_witness
from fourier_physical import comparison_count_witness, block_count_witness
from check_branch_nand_04 import physical_source, replay


def verify(result, words):
    count,witness=result
    assert type(count) is int and count==len(words)
    assert (witness is None)==(not words)
    if witness is not None:assert tuple(witness) in words


def flags(cols,groups,targets):
    buckets={}
    for w in product((0,1),repeat=len(cols)):
        if any(any(w[i] for i in a) and any(w[j] for j in b) for a,b in groups):continue
        s=0
        for c,b in zip(cols,w):
            if b:s^=c
        buckets.setdefault(s,set()).add(w)
    for t in targets:
        words=buckets.get(t,set())
        answer=fourier_count_witness(cols,t,groups)
        verify(answer,words)
        if words:assert tuple(answer[1])==min(words)
    return [len(buckets.get(t,())) for t in targets]


def comparisons(n,edges):
    words=set()
    for w in product((0,1),repeat=n):
        ok=[(w[u]^w[v])==d for u,v,d in edges]
        if all(ok[i] or ok[i+1] for i in range(0,len(ok),2)):words.add(w)
    verify(comparison_count_witness(n,edges),words)
    return len(words)


def physical(k,pins,nand=False):
    words={w for w in product((0,1),repeat=4*k)
           if all((w[u]^w[v])==d for u,v,d in pins)
           and all(w[i:i+2]!=w[i+2:i+4] for i in range(0,4*k,4))}
    answer=block_count_witness(k,pins)
    verify(answer,words)
    if nand:
        source=physical_source(k,pins,suffix=3)
        ones=0
        for bits in product((0,1),repeat=source[0]):
            raw=bits[:4*k]
            t,y0,y1,y2=bits[4*k:]
            expected=raw in words and y0!=y1 and y1==t and y2==raw[0]
            actual=replay(source,bits)
            assert bool(actual)==expected
            ones+=actual
        assert ones==2*answer[0]
        if answer[1] is not None:
            w=tuple(answer[1])
            assert all(replay(source,(*w,t,1^t,t,w[0])) for t in (0,1))
    return len(words)


def main():
    # G has rank two and each orientation spans both bits, but quotienting
    # all targets to zero would report nine words for each of these four fibers.
    assert flags([1,1,2,2],[((0,),(1,)),((2,),(3,))],range(4))==[1,2,2,4]
    assert flags([],[],[0,1])==[1,0]
    flags([0,0,1<<501,1<<501],[((0,),()),((2,),(3,))],[0,1,1<<501])
    assert comparisons(5,[])==32
    assert comparisons(3,[(0,1,0),(1,0,1)]*2)==8
    assert comparisons(4,[(0,1,0),(1,0,0)]*2)==8
    assert comparisons(1,[(0,0,1)]*2)==0
    assert physical(0,[])==1
    assert physical(1,[],True)==12
    assert physical(1,[(0,2,0)]*2,True)==4
    assert physical(1,[(0,2,0),(2,0,1)],True)==0
    assert physical(1,[(0,2,1)],True)==8
    physical(2,[(0,4,1),(1,7,0),(2,5,1),(3,6,0)])
    rng=Random(23091)
    for _ in range(32):
        n=rng.randrange(1,7)
        k=rng.randrange(n+1)
        flags([rng.randrange(8) for _ in range(n)],
              [(tuple(range(k)),tuple(range(k,n)))],range(9))
        comparisons(n,[(rng.randrange(n),rng.randrange(n),rng.randrange(2))
                       for _ in range(2*rng.randrange(5))])
        count=rng.randrange(1,3)
        physical(count,[(rng.randrange(4*count),rng.randrange(4*count),rng.randrange(2))
                        for _ in range(rng.randrange(7))])
    print('Fourier flag, declared vertex, raw gauge and full NAND counts verified')


if __name__=='__main__':main()
