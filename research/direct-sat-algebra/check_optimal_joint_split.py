"""Independent small point-set oracle for optimal joint split and source counts."""
from random import Random
from itertools import combinations
from optimal_joint_split import count,optimal_split
from quadratic_target import evaluate_anf


def spaces(n):
    origin=frozenset([0])
    todo=[origin]; seen={origin}
    while todo:
        s=todo.pop()
        yield s
        for g in set(range(1<<n))-s:
            t=s|{x^g for x in s}
            if t not in seen:
                seen.add(t)
                todo.append(t)


def main():
    rng=Random(1631)
    checks=0
    for n in range(6):
        flats=list(spaces(n))
        for rep in range(7):
            pairs={p:rng.randrange(8) for p in combinations(range(n),2)}
            linear=[rng.randrange(8) for _ in range(n)]
            c=rng.randrange(8)
            vals=[evaluate_anf(c,linear,pairs,x) for x in range(1<<n)]
            best=n
            for f in flats:
                gains={0}
                for x,y in combinations(f,2):
                    h=c^vals[x]^vals[y]^vals[x^y]
                    gains|={v^h for v in gains}
                best=min(best,n-len(f).bit_length()+len(gains).bit_length())
            split=optimal_split(n,pairs)
            assert len(split[0])+len(split[2])==best
            if best:
                assert optimal_split(n,pairs,cap=best-1) is None
            for target in range(8):
                total,w,cost=count(n,c,linear,pairs,target)
                assert total==vals.count(target) and cost==best
                assert (w is None if not total else vals[w]==target)
                checks+=1
    print(f'42 exhaustive subspace optima; {checks} source target counts/witnesses passed.')


if __name__=='__main__':
    main()
