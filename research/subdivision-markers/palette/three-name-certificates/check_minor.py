"""Small independent controls using dual rank and full subset-rank tests."""
from itertools import combinations
from minor_check import _TARGETS, match_excluded_minor, verify_minor


def rank(cols):
    sums = {0}
    for col in cols:
        sums |= {x^col for x in sums}
    return len(sums).bit_length()-1


def check():
    for name, target in _TARGETS.items():
        n = len(target)
        if name.startswith("F7"):
            primal = list(range(1,8))
        else:
            edges = combinations(range(5),2) if n==10 else ((u,v) for u in range(3) for v in range(3,6))
            primal = [(1<<u)|(1<<v) for u,v in edges]
        for mask in range(1<<n):
            s = [i for i in range(n) if mask >> i & 1]
            val = rank(primal[i] for i in s)
            if name!="F7":
                val = len(s)-rank(primal)+rank(primal[i] for i in range(n) if i not in s)
            assert rank(target[i] for i in s)==val
        cols = [2*(x^(x<<2)) for x in reversed(target)]
        label,order = match_excluded_minor(cols)
        assert label==name and verify_minor(cols,order,[],[],name)
        contracted = [x+(i==0) for i,x in enumerate(cols)] + [1,1,123]
        assert verify_minor(contracted,order,[n,n+1],[n+2],name)
        assert not verify_minor(contracted,order,[n,n],[n+2],name)
        assert not verify_minor(contracted,order,[],[n,n+1,n+2],name)
        cols[0] = cols[1]
        assert match_excluded_minor(cols) is None
        assert not verify_minor(cols,order,[],[],name)
    print("four fixed targets, labelled dual ranks, matching and certificate controls passed")


if __name__=="__main__":
    check()
