"""Nine-gate libraries in the sampled cells surviving the component test."""
from functools import reduce
from itertools import combinations_with_replacement, product
from operator import or_
import sys
from h5_prefix_component_batch import catalogue, outcomes
from h5_three_sink_leak_sets import CASES, EDGES, N

indices = (2,8,11,18,29,44,65,114)
singletons = [1 << i for i in range(12)]
edge_bits = (1 << len(EDGES)) - 1

def suffix(scopes,index):
    a,b,c,d = scopes
    def extend(raw):
        return raw | (1024 if a & raw and b & raw else 0) | (2048 if c & raw and d & raw else 0)
    inputs = [extend(row) for row in (*EDGES,*N)]
    cache = {}
    def trace(mask):
        if mask not in cache:
            cache[mask] = sum(1 << i for i,row in enumerate(inputs) if row & mask)
        return cache[mask]
    wanted = edge_bits | sum(1 << (len(EDGES)+i) for i in CASES[index])
    def test(bank):
        terminal = {v | h for v in bank for h in (1024,2048) if v != h}
        for u in terminal:
            if trace(u) & wanted != edge_bits:
                continue
            terms = {trace(x) & trace(y) for x,y in combinations_with_replacement((*bank,u),2)}
            legal = [s for s in terms if not s & ~wanted and s & edge_bits and s & ~edge_bits]
            if reduce(or_,legal,0) != wanted:
                continue
            maximal = [s for s in legal if not any(s != t and s & t == s for t in legal)]
            if any((p | q | r) == wanted for p,q,r in combinations_with_replacement(maximal,3)):
                return True
        return False
    pair_choices = [[s ^ bit for bit in singletons if s & bit] for s in scopes]
    common = (*singletons,*scopes)
    if not test((*common,*set(v for choices in pair_choices for v in choices))):
        return 'relaxed_excluded'
    if any(test((*common,*chosen)) for chosen in product(*pair_choices)):
        return 'passes'
    return 'exact_excluded'

if __name__ == '__main__':
    lo,hi = map(int,sys.argv[1:])
    cells = [(scopes,ix) for scopes in catalogue()
             for ix,status in zip(indices,outcomes(scopes,indices)) if status == 'unknown']
    assert len(cells)==220
    for cursor in range(lo,min(hi,len(cells))):
        scopes,ix=cells[cursor]
        print(cursor,ix,*scopes,suffix(scopes,ix),flush=True)
