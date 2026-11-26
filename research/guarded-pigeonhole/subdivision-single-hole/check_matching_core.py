"""Exhaustive conditional checks for the parity gadgets and small irreducible cores."""
from itertools import product


def fail(x, variables, pattern):
    return all((x>>v)&1==b for v,b in zip(variables,pattern))


def clauses(variables,charge):
    return [(tuple(variables),p) for p in product(range(2),repeat=3) if sum(p)%2!=charge]


def check_graph(edges,n):
    formula=[c for v in range(n) for c in clauses([i for i,e in enumerate(edges) if v in e],int(v==0))]
    one=set()
    for x in range(1<<len(edges)):
        bad=[i for i,(v,p) in enumerate(formula) if fail(x,v,p)]
        assert bad
        if len(bad)==1:one.add(bad[0])
    assert one==set(range(len(formula)))
    for s in range(1,1<<len(edges)):
        touched=sum(any(s>>v&1 for v in vs) for vs,_ in formula)
        assert 3*touched>=8*s.bit_count()


for mask in range(1,8):
    for bits in range(8):
        completions=[x for x in range(8) if (x^bits)&mask==0]
        assert all(x.bit_count()%2==0 for x in completions)==(mask==7 and bits.bit_count()%2==0)
check_graph([(a,b) for a in range(4) for b in range(a)],4)
for k in (3,4):
    edges=[(a*k+i,a*k+(i+1)%k) for a in range(2) for i in range(k)]+[(i,k+i) for i in range(k)]
    check_graph(edges,2*k)
print('Private triple checks and all clause deletions and variable neighborhoods passed for K4 and two prisms.')
