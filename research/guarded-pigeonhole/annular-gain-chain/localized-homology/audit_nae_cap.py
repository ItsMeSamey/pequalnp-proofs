"""Direct cap witnesses and exhaustive local cut tests, including coincident cuts and marks."""
from itertools import permutations, combinations, product
from audit_exterior_product import joined

def cycle(n,seq):
    p=list(range(n))
    for i,x in enumerate(seq):
        p[x]=seq[(i+1)%len(seq)]
    return tuple(p)

def instance(clauses,bits):
    n=len(bits)
    words=[]
    colors=[]
    for i,b in enumerate(bits):
        words.append((2*i,2*i+1))
        colors.extend((b,1-b))
    triples=[]
    for clause in clauses:
        tr=[]
        for lit in clause:
            j=len(colors)
            v=2*(abs(lit)-1)+(lit<0)
            colors.append(colors[v])
            words.append((j,v^1))
            tr.append(j)
        triples.append(tuple(tr))
    size=len(colors)+2
    a,b=size-2,size-1
    sides=[[i for i,c in enumerate(colors) if c==s] for s in (0,1)]
    def cap():
        return cycle(size,[a]+sides[0]+[b]+sides[1])
    for tr in triples:
        if len({colors[x] for x in tr})==1:
            return False
        if joined(cap(),cycle(size,tr),a,b):
            i,j=next((i,j) for i,j in combinations(tr,2) if colors[i]==colors[j])
            side=sides[colors[i]]
            u,v=side.index(i),side.index(j)
            side[u],side[v]=side[v],side[u]
    k=cap()
    assert joined(k,range(size),a,b)
    assert all(not joined(k,cycle(size,row),a,b) for row in words+triples)
    return True

def local():
    count=0
    for n in range(3,7):
        for k in permutations(range(n)):
            for a,b in combinations(range(n),2):
                if not joined(k,range(n),a,b):
                    continue
                arcs=[set(),set()]
                for idx,(start,end) in enumerate(((a,b),(b,a))):
                    x=start
                    while x!=end:
                        arcs[idx].add(x)
                        x=k[x]
                for pair in combinations(range(n),2):
                    split=all(set(pair)&arc for arc in arcs)
                    assert (not joined(k,cycle(n,pair),a,b))==split
                for tr in combinations(range(n),3):
                    if not set(tr)<=arcs[0]|arcs[1]:
                        continue
                    mixed=all(set(tr)&arc for arc in arcs)
                    outcomes=[not joined(k,cycle(n,t),a,b) for t in (tr,tr[::-1])]
                    assert sum(outcomes)==int(mixed)
                count+=1
    return count

if __name__=='__main__':
    fam=[(1,2,3),(-1,2,3),(1,-2,3),(1,2,-3)]
    count=0
    for mask in range(1<<len(fam)):
        clauses=[c for j,c in enumerate(fam) if mask>>j&1]
        for bits in product(range(2),repeat=3):
            pred=all(len({bits[abs(x)-1]^(x<0) for x in c})>1 for c in clauses)
            assert instance(clauses,bits)==pred
            count+=1
    assert not any(instance(fam,bits) for bits in product(range(2),repeat=3))
    assert not any(instance([(1,1,1)],bits) for bits in [(0,),(1,)])
    print(count,'formula/assignment checks; two unsatisfiable fixtures;',local(),'rooted physical cap configurations')

if __name__=='__main__':
    # One variable, three positive occurrences, two extra markers. Any wire may be marked.
    n=7
    rows=[cycle(n,r) for r in [(0,1),(2,1),(3,1),(4,1),(2,3,4)]]
    ct=0
    for k in permutations(range(n)):
        for a,b in combinations(range(n),2):
            assert not joined(k,range(n),a,b) or any(joined(k,h,a,b) for h in rows)
            ct+=1
    print(ct,'exhaustive full cap/root tests on the unsatisfiable repeated-literal fixture')
