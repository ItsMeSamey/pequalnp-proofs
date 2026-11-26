from random import Random
from count_duals import count_duals,echelon_subspaces
from solver import parity


def brute(rank,p,ordinary,fillers,t,target,root_label,moments,dual_tests,s):
    total=0
    for d in range(1<<rank):
        if parity(d&t) or (s is not None and not parity(d&s)) or any(parity(a&d)!=b for a,b in dual_tests):
            continue
        span={0}
        for v,l in ordinary:
            if not parity(d&v):
                x=v|(l<<rank)
                span|={y^x for y in span}
        label=target^root_label^sum(parity(d&m)<<i for i,m in enumerate(moments))
        total+=int((t|(label<<rank)) in span)
    return total


if __name__=='__main__':
    for h,expected in enumerate((1,2,5,16,67,374,2825)):
        assert sum(1 for _ in echelon_subspaces(h))==expected
    rng=Random(8316)
    cases=0
    for _ in range(550):
        rank=rng.randrange(5);p=rng.randrange(3)
        base=[rng.getrandbits(rank+p) for _ in range(rng.randrange(4))]
        fill=base+[v^u for i,v in enumerate(base) for u in base[:i]]
        allcols=fill+[rng.getrandbits(rank+p) for i in range(rng.randrange(7))]
        cols=[(a% (1<<rank),a>>rank) for a in allcols]
        args=(rank,p,cols,range(len(fill)),rng.getrandbits(rank),rng.getrandbits(p),rng.getrandbits(p),
              [rng.getrandbits(rank) for _ in range(p)],
              [(rng.getrandbits(rank),rng.randrange(2)) for j in range(rng.randrange(3))],
              rng.choice([None,rng.getrandbits(rank)]))
        assert count_duals(*args)==brute(*args)
        cases+=1
    # Large count, small quotient: every dual admits many primal representations.
    rank=70
    base=[1<<i for i in range(rank)]
    fill=base+[a^b for i,a in enumerate(base) for b in base[:i]]
    cols=[(v,0) for v in fill]
    assert count_duals(rank,0,cols,range(len(cols)),0)==1<<rank
    print(f"Verified {cases} exact dual counts, seven subspace totals and a 2^70 result.")
