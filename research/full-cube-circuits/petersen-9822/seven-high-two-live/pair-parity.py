"""Compare precursor closure on all three-atom bases, targets and helper pairs."""
from itertools import combinations
cnt=0
def pair(v):return {a|b for a in v for b in v}
for subset in range(128):
    base={m for m in range(1,8) if subset>>(m-1)&1}
    for goal in range(1,8):
        for size in range(3):
            for hh in combinations(set(range(1,8))-{goal},size):
                av=base.copy()
                for _ in range(len(hh)):
                    cand=pair(av);av.update(m for m in hh if m in cand)
                expected=goal in pair(av)
                e={m for m in base if not m&~goal};p=pair(e)
                h=[m for m in hh if not m&~goal]+[0,0];x,y=h[:2];X=x in p;Y=y in p
                if X or Y:
                    if not X and x:X=any((b|y)==x for b in e)
                    if not Y and y:Y=any((b|x)==y for b in e)
                got=goal in p or (X and Y and (x|y)==goal) or any((X and (x|b)==goal)or(Y and (y|b)==goal) for b in e)
                assert expected==got
                cnt+=1
print('three-atom precursor tests',cnt)
