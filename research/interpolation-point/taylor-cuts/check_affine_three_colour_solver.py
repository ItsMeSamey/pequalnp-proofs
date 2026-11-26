"""Compare decoded affine counts to graph coloring and direct flat evaluation."""
from itertools import product
from random import Random
from affine_three_colour_solver import count_three_colour,decode


def main():
    rng = Random(1881)
    identity,swap,cycle = (1,2,3),(2,1,3),(2,3,1)
    cases = [([],3,True), ([(0,1,identity)],3,True)]
    for perm in (identity,swap,cycle):
        cases.append(([(0,1,identity),(1,2,identity),(0,2,perm)],4,perm!=cycle))
    cases.append(([(i,j,identity) for i in range(4) for j in range(i+1,4)],4,True))
    checked = 0
    for edges,size,recognized in cases:
        for rep in range(6):
            n=2*size+1
            normals=[1<<i for i in range(n)]
            for _ in range(5*n):
                i,j=rng.sample(range(n),2)
                normals[i]^=normals[j]
            shift=rng.randrange(1<<n)
            def normal(i,color):
                p,q=normals[2*i:2*i+2]
                return (q,p,p^q)[color-1]
            planes=[tuple(normals[2*i:2*i+2]) for i in range(size)]
            for i,j,perm in edges:
                planes.extend((normal(i,c),normal(j,perm[c-1])) for c in (1,2,3))
            # Local point 00 is forbidden. Each of the three other words is
            # the unique allowed word annihilated by its corresponding normal.
            flats=[]
            for p,q in planes:
                if rng.randrange(2):
                    q ^= p
                flats.append(((p,(p&shift).bit_count()%2),(q,(q&shift).bit_count()%2)))
            rng.shuffle(flats)
            assert decode(n,flats) is not None
            answer=count_three_colour(n,flats)
            graph_count=sum(all(word[j]!=perm[word[i]-1] for i,j,perm in edges)
                            for word in product((1,2,3),repeat=size))
            actual=[x for x in range(1<<n) if all(any((p&x).bit_count()%2!=a for p,a in flat)
                                                   for flat in flats)]
            assert graph_count*2==len(actual)
            if recognized:
                count,witness=answer
                assert count==len(actual) and (witness in actual if count else witness is None)
            else:
                assert actual and answer is None
            checked+=1
    assert count_three_colour(2,[])==(4,0)
    print(f"{checked} dense signed controls matched graph/affine enumeration, including fixed-point and frustrated cycles")


if __name__=='__main__':
    main()
