"""Finite two-output algebra for a split-use sequential pair of shared mixed gates."""
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import sys

def audit(b):
    raw = tuple(sum(1<<row for row in range(1<<(b+1)) if row>>i&1) for i in range(b+1))
    allbits = (1<<(1<<(b+1)))-1
    # A pair of truth tables gives the T- and U-activated values. The last
    # variable is R, the T-only private factor inside the downstream endpoint.
    @lru_cache(None)
    def variants(mask, nx, ny):
        if mask.bit_count()+nx+ny==1:
            if nx:return {(allbits,0)}
            if ny:return {(raw[-1],allbits)}
            val=raw[mask.bit_length()-1]
            return {(val,val)}
        result=set()
        for left,right in splits(mask,nx,ny):
            for f,g in variants(*left):
                for h,k in variants(*right):
                    result.add((f&h,g&k))
                    result.add((f|h,g|k))
        return result
    def splits(mask,nx,ny):
        for lm,lx,ly in product(range(mask+1),range(nx+1),range(ny+1)):
            if lm&~mask:continue
            left=(lm,lx,ly)
            right=(mask^lm,nx-lx,ny-ly)
            if any(left) and any(right) and left<=right:
                yield left,right
    def nonzero_or_splits(counts, pair):
        for left,right in splits(*counts):
            for f,g in variants(*left):
                if (f,g)==(0,0):continue
                for h,k in variants(*right):
                    if (h,k)!=(0,0) and (f|h,g|k)==pair:
                        yield left,(f,g),right,(h,k)
    # Also permit fewer special leaves at the ordinary OR attachments, since
    # the other uses may instead occur at AND attachments.
    all_counts=[((1<<b)-1,nx,ny) for nx,ny in product(range(2),range(3))
                if b+nx+ny]
    targets=set().union(*(variants(*cnt) for cnt in all_counts))
    initial=frozenset((0,allbits,*raw))
    states={initial}
    hard=targets.copy()
    two_gate_states=[]
    for depth in range(b+2):
        if depth<=2:two_gate_states.extend(states)
        for state in states:
            hard.difference_update(product(state,state))
        if depth==b+1 or not hard:break
        states={state|{h} for state in states for x,y in combinations(state,2)
                for h in (x&y,x|y) if h not in state}
    if b<3:assert not hard
    else:
        assert len(hard)==12
        half=1<<(1<<b)
        for f,g in hard:
            f0,f1=f%half,f//half
            g0,g1=g%half,g//half
            assert g0==g1 and not (f0&~g0 or g0&~f1)
            assert any(g in state for state in two_gate_states)
            for cnt in all_counts:
                if (f,g) not in variants(*cnt):continue
                for l,lf,r,rf in nonzero_or_splits(cnt,(f,g)):
                    assert not any(nonzero_or_splits(l,lf))
                    assert not any(nonzero_or_splits(r,rf))
    print(b,len(targets),len(hard))
if __name__=='__main__':
    for b in range(4):audit(b)
