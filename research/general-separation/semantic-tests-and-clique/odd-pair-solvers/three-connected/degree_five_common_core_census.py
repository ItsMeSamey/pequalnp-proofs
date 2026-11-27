"""Root-core census, both named degrees 3 or 5, nonempty C and nonempty exterior."""
from collections import Counter
from pathlib import Path
import json
from itertools import combinations,permutations,product


def census(c,a,b):
    # Labels: p,q,A,B,C; a<=b. Both pins are nonadjacent.
    A=tuple(range(2,2+a));B=tuple(range(2+a,2+a+b));C=tuple(range(2+a+b,2+a+b+c))
    n=2+a+b+c
    rows=[0]*n
    def toggle(i,j):
        rows[i]^=1<<j
        rows[j]^=1<<i
    for i in A+C:toggle(0,i)
    for i in B+C:toggle(1,i)
    for i,j in product(A,B):toggle(i,j)
    if sum(rows[i].bit_count()<5 for i in A+B)<3:
        return 0,{}
    edges=[(i,j) for i,j in combinations(range(2,n),2)
           if not rows[i]>>j&1 and rows[i].bit_count()<5 and rows[j].bit_count()<5]
    slots=list(combinations(range(2,n),2))
    maps=[]
    for aa,bb,cc in product(permutations(A),permutations(B),permutations(C)):
        maps.append(aa+bb+cc)
        if a==b:maps.append(bb+aa+cc)
    results={}
    count=0
    def visit(k):
        nonlocal count
        if sum(rows[i].bit_count()<5 for i in A+B)<3:
            return
        if k<len(edges):
            i,j=edges[k]
            visit(k+1)
            if max(rows[i].bit_count(),rows[j].bit_count())<5:
                toggle(i,j)
                visit(k+1)
                toggle(i,j)
            return
        if any(rows[i].bit_count() not in (3,5) for i in C):
            return
        for s in range(3,1<<n,4):
            if s.bit_count()%2==0 and all((row&s).bit_count()%2 for i,row in enumerate(rows) if s>>i&1):
                return
        count+=1
        key=min(sum(((rows[p[i-2]]>>p[j-2])&1)<<t for t,(i,j) in enumerate(slots)) for p in maps)
        results[key]=results.get(key,0)+1
    visit(0)
    return count,results


def record(c,a,b,key,multiplicity):
    n=2+a+b+c
    rows=[0]*n
    def join(i,j):
        rows[i] |= 1<<j
        rows[j] |= 1<<i
    for i in range(2,n):
        if i<2+a or i>=2+a+b:join(0,i)
        if i>=2+a:join(1,i)
    for bit,(i,j) in enumerate(combinations(range(2,n),2)):
        if key>>bit&1:join(i,j)
    options=[[target-rows[i].bit_count() for target in (3,5) if target>=rows[i].bit_count()]
             for i in range(2,2+a+b)]
    # Shrink a connected auxiliary exterior to a virtual hub. For each deletion
    # of at most two core vertices, each surviving core piece must reach a port.
    ports=sum(1<<i for i,opts in enumerate(options,2) if max(opts)>0)
    feasible=True
    for cut in [()]+list(combinations(range(n),1))+list(combinations(range(n),2)):
        live=((1<<n)-1)^sum(1<<i for i in cut)
        reached=ports&live
        last=-1
        while last!=reached:
            last=reached
            for i in range(n):
                if reached>>i&1:reached |= rows[i]&live
        if reached!=live:
            feasible=False
            break
    return dict(mask=key,labelled=multiplicity,rows=rows,exterior_degrees=options,
                ports=ports.bit_count(),all_pieces_reach_port=feasible)


def main():
    data=[]
    for c in range(1,6):
        sizes=[d-c for d in (3,5) if d>=c]
        for i,a in enumerate(sizes):
            for b in sizes[i:]:
                total,orbits=census(c,a,b)
                rec=[record(c,a,b,k,orbits[k]) for k in sorted(orbits)]
                data.append(dict(c=c,a=a,b=b,labelled=total,orbits=rec))
                print((c,a,b),total,len(rec),sum(x['all_pieces_reach_port'] for x in rec))
    out=Path(__file__).with_name('degree_five_common_core_census.json')
    data=json.dumps(data,indent=2)+'\n'
    if out.exists():
        assert out.read_text()==data
    else:
        out.write_text(data)


if __name__=='__main__':
    main()
