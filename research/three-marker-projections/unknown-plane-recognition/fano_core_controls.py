from random import Random
from clause_triangles import compile_matching
from triangle_cut import cut_decide

for seed in range(6):
    rng=Random(933+seed)
    axes=list(range(7))
    rng.shuffle(axes)
    lines=[(i,(i+1)%7,(i+3)%7) for i in range(7)]
    rng.shuffle(lines)
    blocks=[[[(axes[v],s) for v in line] for s in (0,1)] for line in lines]
    for drop in (False,True):
        f=[c for b in (blocks[1:] if drop else blocks) for c in b]
        truth=any(all(any((x>>v&1)^s for v,s in c) for c in f) for x in range(128))
        assert truth==drop
        inst=compile_matching(7,f)
        assert inst is not None
        x,w,size=cut_decide(7,f)
        assert (x is not None)==truth
        print(seed,'SAT' if truth else 'UNSAT',inst[-1],w,size)
