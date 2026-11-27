"""Scheduled 04-only independent flag, signed-vertex and NAND witness checks."""
from itertools import product
from random import Random
from syndrome_dp import syndrome_witness
from syndrome_physical import syndrome_comparison_witness, syndrome_block_witness
from check_mux_single_block_04 import physical_chart
from check_branch_nand_04 import physical_source, replay

METHODS=('dp','orientation','auto')


def check(cols,targets,groups):
    def encode(word):
        y=0
        for b,c in zip(word,cols):
            if b:y^=c
        return y
    def legal(w):
        return all(not(any(w[i] for i in a) and any(w[i] for i in b)) for a,b in groups)
    actual={encode(w) for w in product((0,1),repeat=len(cols)) if legal(w)}
    for target in targets:
        for method in METHODS:
            word=syndrome_witness(cols,target,groups,method=method)
            assert (word is not None)==(target in actual)
            if word is not None:
                assert len(word)==len(cols) and all(b in (0,1) for b in word)
                assert legal(word) and encode(word)==target


def run_flags():
    check([], [0,1,1<<1400], [])
    check([0,0],[0,1], [((0,),(1,))])
    h=1<<4096
    check([h,h,0,h^2,2], [0,2,h,h^2,h^4], [((0,1),(2,)),((),(3,))])
    # Separate pieces: first has two groups and rank two; second one group and rank four.
    check([1,2,1,2,4,8,16,32], range(64),
          [((0,),(1,)),((2,),(3,)),((4,5),(6,7))])
    check([1,3,2,3,4,7,1],range(8),[((0,1),(2,3)),((4,),(5,))])
    for cols,target in [([-1],0),([1],-1)]:
        try:syndrome_witness(cols,target,[],method='dp')
        except ValueError:pass
        else:raise AssertionError('negative mask accepted')
    rng=Random(6781)
    for _ in range(60):
        n=rng.randrange(8)
        cols=[rng.randrange(8) for _ in range(n)]
        groups=[]
        i=0
        while i<n:
            end=rng.randrange(i+1,min(n,i+4)+1)
            cut=rng.randrange(i,end+1)
            if rng.randrange(4):groups.append((tuple(range(i,cut)),tuple(range(cut,end))))
            i=end
        check(cols,range(9),groups)


def physical(n,rows):
    ports,pins=physical_chart(rows)
    source=physical_source(len(rows),pins,suffix=3)
    edges=tuple(e for row in rows for e in row)
    truth=set()
    for x in product((0,1),repeat=n):
        valid=all(any((x[u]^x[v])==d for u,v,d in row) for row in rows)
        raw=tuple(x[v]^off for v,off in ports)
        assert bool(replay(source,(*raw,0,1,0,raw[0])))==valid
        if valid:truth.add(x)
    for method in METHODS:
        opts=dict(method=method,guarantee='auto')
        result=syndrome_comparison_witness(n,edges,**opts)
        assert (result is not None)==bool(truth)
        if result is not None:assert tuple(result) in truth
        raw=syndrome_block_witness(len(rows),pins,**opts)
        assert (raw is not None)==bool(truth)
        if raw is None:continue
        assert all((raw[a]^raw[b])==s for a,b,s in pins)
        for g,a,b,c in product((0,1),repeat=4):
            assert bool(replay(source,(*raw,g,a,b,c)))==(a!=b and b==g and c==raw[0])


def main():
    run_flags()
    A,B,C=(0,0,1),(0,1,0),(1,0,1)
    for d in (0,1):
        physical(2,[(A,B),(B,C),(C,(1,1,d))])
    for sign in (0,1):
        physical(3,[((1,0,sign),(2,1,0)),((0,2,0),(2,1,0))])
    # Disjoint-ended pair: exact G=0 fallback still has to solve the signed source.
    physical(4,[((0,1,1),(2,3,0)),((0,1,0),(2,3,1))])
    assert syndrome_block_witness(1,[(0,1,0),(1,0,1)],method='dp') is None
    print('three methods; raw flag fibers, sparse high masks, signed offsets, physical NAND replay')


if __name__=='__main__':main()
