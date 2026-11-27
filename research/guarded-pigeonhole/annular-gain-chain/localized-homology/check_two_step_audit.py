"""Independently compare complement matching, cap traversal and two-token propagation."""
from itertools import permutations,combinations
from random import Random


def recognized(table):
    n=len(table[0]);base=range(n)
    for a,b in combinations(base,2):
        for u,v in permutations(base,2):
            if any(h[a]==u or h[b]==v for h in table):continue
            # Find a perfect matching of bad pairs using augmenting paths.
            matched={}
            def augment(c,seen):
                for t in base:
                    if t in (u,v) or t in seen:continue
                    if any((h[a]==t and h[c]==u) or (h[b]==t and h[c]==v) for h in table):continue
                    seen.add(t)
                    if t not in matched or augment(matched[t],seen):
                        matched[t]=c;return True
                return False
            if all(augment(c,set()) for c in base if c not in (a,b)):return False
    return True


def raw(table):
    n=len(table[0])
    for k in permutations(range(n)):
        joined=set()
        for h in table:
            p=[k[v] for v in h]
            for i,j in enumerate(p):
                for w in (j,p[j]):
                    if w!=i:joined.add(tuple(sorted((i,w))))
        if len(joined)!=n*(n-1)//2:return False
    return True


def twotokens(n,gates,a,b):
    current={(a,b)}
    for gate in gates:
        rotate=dict(zip(gate,gate[1:]+gate[:1]))
        current|={(rotate.get(x,x),rotate.get(y,y)) for x,y in current}
    return current


if __name__=='__main__':
    r=Random(80421);total=passing=0
    for n in range(2,7):
        ps=list(permutations(range(n)))
        tables=([p for j,p in enumerate(ps) if m>>j&1] for m in range(1,1<<len(ps))) if n<=3 else (r.sample(ps,r.randrange(1,min(16,len(ps))+1)) for _ in range(125))
        for T in tables:
            a=recognized(T)
            if a!=raw(T):raise AssertionError(T)
            total+=1;passing+=a
    count=0
    for n in range(3,9):
        for rep in range(30):
            gates=[r.sample(range(n),3) for _ in range(rep%8)]
            table={tuple(range(n))}
            for g in gates:
                rot=dict(zip(g,g[1:]+g[:1]))
                table|={tuple(rot.get(x,x) for x in h) for h in table}
            for a,b in permutations(range(n),2):
                if twotokens(n,gates,a,b)!={(h[a],h[b]) for h in table}:raise AssertionError(gates)
                count+=1
    print(total,'table comparisons,',passing,'passing;',count,'two-token comparisons')
