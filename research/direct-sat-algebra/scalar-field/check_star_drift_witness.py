from itertools import product
from random import Random
from punctured_witness import BinaryField
from star_drift_witness import solve


def check():
    f=BinaryField(7)
    rng=Random(5991)
    rows=[]
    # First principal determinant has all three smaller encodings as roots.
    for j in range(3):
        rows.append((j+1,0,2,[(j+1,j),(5+j,1),(4,1)]))
    # Dense lower-left and second diagonal block; repeated coefficient terms included.
    for j in range(3):
        rows.append((4,5+j,3,[(k,rng.randrange(4)) for k in range(9)]+[(8,2),(8,2)]))
    for _ in range(64):
        target=[rng.randrange(4) for _ in rows]
        res=solve(f,9,rows,target)
        assert res.status=="SAT" and res.values[0]==3 and 5<=res.center_trials<=8
        for (u,v,c,terms),b in zip(rows,target):
            a=c^f.mul(res.values[u],res.values[v])
            for i,k in terms:a ^= f.mul(k,res.values[i])
            assert a==b
    degree_four=[(0,j+1,1,[(j+1,j)]) for j in range(4)]
    assert solve(f,5,degree_four).status=="UNKNOWN"
    assert not any(all(f.mul(p[0]^j,p[j+1])==1 for j in range(4))
                   for p in product(range(4),repeat=5))
    assert solve(f,3,[]).values==(0,0,0)
    assert solve(f,3,[(0,1,0,[(2,1)])],[2]).status=="SAT"
    print("64 dense mixed degree-three targets, sharp four-trial center, unsatisfiable degree-four star, empty and single-edge cases passed")


if __name__=="__main__":
    check()
