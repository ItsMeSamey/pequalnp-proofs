"""Small strict terminal-label and fixed-physical-ground obstruction checks."""
from itertools import combinations,product
from check import elimination,equal,partitions


def rowspace(labels,blocks):
    result=[]
    for part in blocks:
        q=0
        for i in part:
            q^=labels[i]
        result.append(q)
    return result


def test():
    good=((0,1),(2,3))
    wrong=[p for p in partitions(4) if p!=good]
    arrays=0
    for r in (0,1,2):
        for L in product(range(1<<r),repeat=4):
            wanted=rowspace(L,good)
            assert any(equal(wanted,rowspace(L,p)) for p in wrong)
            arrays+=1
    hyperplanes=0
    for d in range(3,9):
        A=[1<<i for i in range(d)]+[(1<<i)^(1<<j) for i,j in combinations(range(d),2)]+[7]
        for f in range(1,1<<d):
            subset=[v for v in A if not (v&f).bit_count()%2]
            assert len(elimination(subset)[0])==d-1
            hyperplanes+=1
    print(arrays,"all low-root two-pair label arrays excluded;",hyperplanes,"nongraphic hyperplane spans")


if __name__=="__main__":
    test()
