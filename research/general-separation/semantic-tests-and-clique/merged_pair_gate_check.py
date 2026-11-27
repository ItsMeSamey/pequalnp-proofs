"""Verify the component criterion with exposed selections kept fixed."""
from itertools import combinations, product
from mixed_quadratic_projection import ROWS, C


def physical_ports():
    choices = {s:set() for s in range(4)}
    for word in range(256):
        defects=C^sum((((r&word).bit_count()%2)<<i) for i,r in enumerate(ROWS))
        if not word&defects&126:
            s=(word&1)|((word>>6)&2)
            choices[s].add((defects&1)|((defects>>6)&2))
    return choices


def possible(n,edges,word,choices):
    parities={0}
    for u,v in edges:
        s=((word>>u)&1)|(((word>>v)&1)<<1)
        effects={((m&1)<<u)|(((m>>1)&1)<<v) for m in choices[s]}
        parities={p^d for p in parities for d in effects}
    return {d for d in range(1<<n) if any(not((d^p)&word) for p in parities)}


def criterion(n,edges,word,drift):
    graph=[[] for _ in range(n)]
    for u,v in edges:
        graph[u].append(v)
        graph[v].append(u)
    seen=set()
    for start in range(n):
        if start in seen:
            continue
        comp=[start]
        seen.add(start)
        for i in comp:
            for j in graph[i]:
                if j not in seen:
                    seen.add(j)
                    comp.append(j)
        if sum(len(graph[i]) for i in comp)!=2*(len(comp)-1):
            continue
        if all(word>>i&1 and (drift>>i&1)==(1^(len(graph[i])&1)) for i in comp):
            return False
    return True


def main():
    choices=physical_ports()
    assert choices=={0:set(range(4)),1:set(range(4)),2:set(range(4)),3:{1,2,3}}
    seen=0
    for n in range(2,6):
        pairs=list(combinations(range(n),2))
        hosts=[e for k in range(min(4,len(pairs))+1) for e in combinations(pairs,k)]
        hosts += [((0,1),(0,1))]
        for edges in hosts:
            for w in range(1<<n):
                assert possible(n,edges,w,choices)=={d for d in range(1<<n)
                                                    if criterion(n,edges,w,d)}
                seen+=1<<n
    print(seen,"occupied-set/drift tests including repeated edges")
    # Readouts force 0,1. Drift at 0 is the independent terminal bit at 2.
    ok=[w for w in range(16) if w&3==3 and criterion(4,[(0,1),(2,3)],w,(w>>2)&1)]
    assert min(w.bit_count() for w in ok)==3


if __name__=="__main__":
    main()
