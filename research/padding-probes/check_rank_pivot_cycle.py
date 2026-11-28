"""Independent full-model certificate for the cycle's two cover optima."""
from itertools import combinations
from source_remote_pivot_rank import solve


def rank(cols):
    pivots = {}
    for word in cols:
        while word:
            p = word.bit_length()-1
            if p not in pivots:
                pivots[p] = word
                break
            word ^= pivots[p]
    return len(pivots)


def union(words):
    acc = 0
    for word in words:
        acc |= word
    return acc


def check(m):
    a,b,c = ([3*i+t for i in range(m)] for t in (1,2,3))
    n = 3*m+1
    background = [(-x,-y) for x,y in zip(a,b)]
    triples = list(zip(a,b,c))
    for i in range(m):
        j = (i+1)%m
        for x,y in ((a[i],c[i]),(-b[i],c[i]),(c[i],c[j]),(-c[i],-c[j])):
            triples.extend(((x,y,n),(x,y,-n)))
    def true(word,lit):
        return ((word >> (abs(lit)-1)) & 1) == (lit>0)
    models = [word for word in range(1 << n)
              if all(any(true(word,lit) for lit in row) for row in background)]
    full = (1 << len(models))-1
    literal = {}
    for v in range(1,n+1):
        literal[v] = sum(1 << j for j,word in enumerate(models) if true(word,v))
        literal[-v] = full ^ literal[v]
    failures = []
    covers = [0]*(n+1)
    for i,row in enumerate(triples):
        masks = tuple(literal[v] for v in row)
        failures.append(full ^ union(masks))
        singles = [masks[j] & ~(masks[(j+1)%3] | masks[(j+2)%3]) for j in range(3)]
        assert all(singles), ('unconditionally reducible',i)
        for v in range(1,n+1):
            if all(any(not (s & literal[p]) for s in singles) for p in (v,-v)):
                covers[v] |= 1 << i
    valid = [w for w in models if all(any(true(w,lit) for lit in row) for row in triples)]
    expected = 0 if m%2 else 4*3**(m//2)
    assert len(valid) == expected
    def covered_rank(mask):
        return rank(col for i,col in enumerate(failures) if mask >> i & 1)
    target = rank(failures)
    assert target and covered_rank(0)==0 and covered_rank(covers[n])==target
    all_rows = (1 << len(triples))-1
    assert all(union(covers[v] for v in vs)!=all_rows for k in range(m)
               for vs in combinations(range(1,n+1),k))
    assert union(covers[v] for v in c)==all_rows
    ans = solve(n,background+triples)
    assert ans['status']==('SAT' if expected else 'UNSAT')
    assert len(ans['pivots'])==1 and covered_rank(covers[ans['pivots'][0]])==target
    assert ans['metrics']['rank']==target
    if expected:
        assert sum(1 << (v-1) for v in ans['true_variables']) in valid
    else:
        assert ans['true_variables'] is None
    print(dict(m=m,models=len(valid),ordinary_opt=m,rank_opt=1,rank=target,
               selected=ans['pivots'],status=ans['status']))


if __name__=='__main__':
    for length in (3,4):
        check(length)
