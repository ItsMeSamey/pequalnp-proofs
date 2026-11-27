"""End-to-end physical decision and witness comparisons on small networks."""
from itertools import combinations_with_replacement, permutations
from random import Random

from native_solver import IncompatiblePortOrder, solve_native


def same(sigma, mask, a,b):
    start=a
    while True:
        if a==b:
            return True
        g=a//3
        a=sigma[3*g+(a%3+((mask>>g)&1))%3]
        if a==start:
            return False


def planar_by_rotations(sigma):
    # Enumerate all 2^g physical vertex rotations independently of wheel planarity.
    n=len(sigma);g=n//3
    components=list(range(g))
    for i,j in enumerate(sigma):
        old,new=components[j//3],components[i//3]
        components=[new if x==old else x for x in components]
    target=2*len(set(components))+2*g
    def faces(mask):
        seen=set();count=0
        for v in range(n):
            if v in seen:continue
            count+=1
            while v not in seen:
                seen.add(v)
                h=v//3
                v=sigma[3*h+(v%3+((mask>>h)&1))%3]
        return count
    values=[faces(i) for i in range(1<<g)]
    return any(v+values[-1-i]==target for i,v in enumerate(values))


def run():
    rng=Random(1759)
    instances=[p for p in permutations(range(3))]
    for g,count in [(2,42),(3,50),(4,50),(5,20),(6,10)]:
        for _ in range(count):
            instances.append(rng.sample(range(3*g),3*g))
    # Interleaved component names retain their original mask indices.
    instances.append([0,6,2,3,9,5,1,7,8,4,10,11])
    for g in (3,4,5,6,8):
        perm=list(range(3*g))
        for i in range(g-1):
            a,b=3*i+2,3*(i+1)
            perm[a],perm[b]=perm[b],perm[a]
        instances.append(perm)
    queries=hits=rejected=compatible=0
    for sigma in instances:
        n=len(sigma)
        admitted=planar_by_rotations(sigma)
        roots=list(combinations_with_replacement(range(n),2))
        if len(roots)>20:
            roots=rng.sample(roots,20)
        for a,b in roots:
            try:
                mask=solve_native(sigma,a,b)
            except IncompatiblePortOrder:
                if admitted:raise AssertionError(("wrong rejection",sigma))
                rejected+=1
                break
            if not admitted:raise AssertionError(("wrong recognition",sigma))
            possible=any(same(sigma,m,a,b) for m in range(1<<(n//3)))
            if possible!=(mask is not None) or (possible and not same(sigma,mask,a,b)):
                raise AssertionError((sigma,a,b,mask))
            queries+=1;hits+=possible
        else:
            compatible+=1
    print(compatible,'compatible networks,',rejected,'incompatible,',queries,'queries,',hits,'verified masks,',queries-hits,'negative')


if __name__=='__main__':
    run()
