"""Independent H8 decision checker. No imports from original prototype.
CLI: residual cardinality, batch cap, exception cap, first and last numerical masks.
"""
from functools import lru_cache
from itertools import combinations
import sys

vertices = (0, 1, 2, 4, 5, 8, 9, 10)
edges = ((0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(4,8),(4,10),(5,8),(5,9),(8,9))
extra = ((3,6),(3,7),(6,7),(6,10),(7,9))
bits = {v: 1<<i for i,v in enumerate(vertices)}
edge_masks = [bits[a]|bits[b] for a,b in edges]
independent = {s for s in range(256) if all(s&e != e for e in edge_masks)}
# Supersets of maximal independent sets need no extra checks.
tests = [s for s in independent if all((s|b) not in independent for b in bits.values() if not s&b)]
def vector(items):
    return sum(1<<x for x in set(items))
def matrix(rows):
    return int.from_bytes(b''.join(r.to_bytes(32,'little') for r in rows),'little')
@lru_cache(maxsize=512)
def disjoin_rows(left,right):
    return matrix(right if left>>i&1 else 0 for i in range(256))
columns = (1<<256)-1
absent = [vector(i for i in range(256) if i&s==0) for s in tests]
hit = [vector(i for i in range(256) if i&e) for e in edge_masks]
@lru_cache(None)
def clause_candidates(r):
    if not r: return columns
    b = r&-r
    return hit[b.bit_length()-1] & clause_candidates(r-b)

def solve(u,k,m):
    neighborhoods = {i:0 for i in range(11)}
    for i,(a,b) in enumerate(edges+extra):
        if i<len(edges) and u>>i&1: continue
        neighborhoods[a] |= bits.get(b,0)
        neighborhoods[b] |= bits.get(a,0)
    primitive = [s for s in range(256) if s in bits.values() or any(s&v==s for v in neighborhoods.values())]
    guard = vector(primitive)
    binary = {a|b for a in primitive for b in primitive}
    joined = vector(binary)
    choices = matrix((1 if m==1 else joined | vector(i|b for b in primitive)) if i in binary else 0 for i in range(256))
    @lru_cache(None)
    def one(r):
        eligible = clause_candidates(r)
        allowed = choices
        for avoid in absent:
            separating = eligible&avoid
            if separating&guard: continue
            # Either globally selected clause separates this maximal independent set.
            allowed &= disjoin_rows(separating,columns) | disjoin_rows(columns,separating)
            if not allowed: break
        return allowed
    @lru_cache(None)
    def cover(r,n):
        answer = one(r)
        if n<=1 or answer==choices: return answer
        # Allocate the highest remaining edge to the first batch. Generate subsets by combinations.
        e = 1<<(r.bit_length()-1)
        others = [1<<i for i in range(11) if (r^e)>>i&1]
        for size in range(len(others)):
            for group in combinations(others,size):
                g = e+sum(group)
                feasible = one(g)
                if feasible: answer |= feasible & cover(r^g,n-1)
                if answer==choices: return answer
        return answer
    return bool(cover(u,k))

if __name__=='__main__':
    n,k,m,lo,hi=map(int,sys.argv[1:])
    for u in range(lo,hi+1):
        if u.bit_count()==n:
            print(u,int(solve(u,k,m)),flush=True)
