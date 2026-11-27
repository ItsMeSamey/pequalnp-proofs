"""Tiny chart-enumeration reference for semantic closure in the conflict DAG."""
from functools import reduce
from itertools import combinations
from operator import or_
from conflict_compare import conflict,restrict
from wedge_path import insert,wedge
from frontier import basis
from recognizer import bit_indices,tag_at

def first_on_support(cols,mask):
    d=max((cols[i][0].bit_length() for i in bit_indices(mask)),default=0)
    seq=[]
    for g in range(1<<(2*d)):
        piv={}
        for i in bit_indices(mask):
            k,b=cols[i]
            if tag_at(g,k,d)!=b: continue
            z=1<<i
            while k:
                p=k.bit_length()-1
                if p not in piv:
                    piv[p]=(k,z)
                    break
                old,other=piv[p]
                k ^= old; z ^= other
            if not k: seq.append(z)
    return basis(seq)

def solve(cols):
    out={}
    masks,states={},set()
    stack=[(1<<len(cols))-1]
    while stack:
        mask=stack.pop()
        if mask in masks: continue
        R=first_on_support(cols,mask)
        masks[mask]=R
        if R in states: continue
        states.add(R)
        if len(R)<2: continue
        C=conflict(cols,reduce(or_,R,0))
        if C:
            stack.extend({reduce(or_,restrict(R,i),0) for i in bit_indices(C)})
        else:
            for u,v in combinations(R,2):
                z=wedge(u,v)
                insert(out,z,(u,v,z))
    return [a for _,a in out.values()],len(states),len(masks)
