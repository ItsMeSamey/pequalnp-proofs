"""Every simple core on five vertices, tested via independent enumerations."""
from itertools import combinations


def core(n,edges):
    sets=[]
    def visit(i,used):
        if i==len(edges):
            sets.append(set(range(n))-used)
        else:
            visit(i+1,used)
            a,b=edges[i]
            if a not in used and b not in used: visit(i+1,used|{a,b})
    visit(0,set())
    return sets


def exchange(family):
    return all(any((a-{v})|{w} in family for w in b-a)
               for a in family for b in family for v in a-b)


if __name__=="__main__":
    pairs=list(combinations(range(5),2))
    for mask in range(1<<len(pairs)):
        exposed=core(5,[e for j,e in enumerate(pairs) if mask>>j&1])
        d=min(map(len,exposed))
        maximal=[s for s in exposed if len(s)==d]
        assert exchange(maximal)
        for m in range(32):
            P={v for v in range(5) if m>>v&1}
            assert exchange([s for s in maximal if s<=P])
    assert not exchange([s for s in core(4,[(0,1),(1,2),(2,3)]) if len(s)==2])
    print("1024 cores, 32768 reservoir supports, P4 failure confirmed")
