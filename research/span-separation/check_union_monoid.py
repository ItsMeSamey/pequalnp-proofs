"""Compare stable SAT assignments to exact two-part connected pin colourings."""
from itertools import product
from random import Random

rng=Random(2026401)
runs=0
for nv in range(1,6):
    literals=[(i,p) for i in range(nv) for p in (0,1)]
    for _ in range(35):
        clauses=[rng.sample(literals,rng.randint(1,min(len(literals),3))) for j in range(rng.randint(2,6))]
        sat=any(all(any(assignment[i]==p for i,p in clause) for clause in clauses) for assignment in product((0,1),repeat=nv))
        m=len(clauses)
        n=2*nv+2+m
        f1,f2=2*nv,2*nv+1
        c0=2*nv+2
        adj=[set() for _ in range(n)]
        def edge(i,j):
            adj[i].add(j);adj[j].add(i)
        for i in range(nv-1):
            for p in (0,1):
                for pp in (0,1): edge(2*i+p,2*(i+1)+pp)
        for p in (0,1):
            edge(f1,p);edge(f2,2*(nv-1)+p)
        for j,cl in enumerate(clauses):
            for i,p in cl: edge(c0+j,2*i+p)
        def conn(S):
            seen={next(iter(S))}
            todo=list(seen)
            while todo:
                v=todo.pop()
                for w in (adj[v]&S)-seen:
                    seen.add(w);todo.append(w)
            return seen==S
        def accepts(mask):
            red={f1,f2}|{i for i in range(2*nv) if mask>>i&1}
            return conn(red) and conn(set(range(n))-red)
        assert sat==any(accepts(mask) for mask in range(1<<(2*nv)))
        runs+=1
print(f"{runs} SAT ladders checked exhaustively")
