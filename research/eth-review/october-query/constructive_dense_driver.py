"""Original-assignment counting with polynomially many legal sparse trials."""
from collections import Counter
from itertools import combinations
from math import comb
from constructive_tanner import distance_rows, modulus, multiply
from original_dense_driver import direct_count, leaves, threshold, count_query

def legal_masks(m,P):
    h=min(m,P)
    Q=1<<((100*m-1).bit_length())
    H=1<<((64*h-1).bit_length())
    if sum(comb(m,j) for j in range(1,h+1))<=Q*Q*H*H:
        for j in range(1,h+1):
            for indices in combinations(range(m),j):
                yield sum(1<<i for i in indices)
        return
    mod1,mod2=modulus(Q.bit_length()-1),modulus(H.bit_length()-1)
    for a in range(Q):
        ax=[multiply(a,j,mod1) for j in range(h)]
        for b in range(Q):
            bits=[1<<((u^b)%m) for u in ax]
            for x in range(H):
                pw=[1]
                for j in range(1,h):
                    pw.append(multiply(pw[-1],x,mod2))
                # The row depends linearly on y. Compute all basis masks once per x.
                basis=[]
                for k in range(H.bit_length()-1):
                    row=0
                    for v,bit in zip(pw,bits):
                        if multiply(1<<k,v,mod2)&1:
                            row^=bit
                    basis.append(row)
                row=0
                for index in range(1,H):
                    row^=basis[(index&-index).bit_length()-1]
                    if row:
                        yield row

def count(n,clauses,stats=None):
    f=[tuple(c) for c in clauses]
    if n<0 or any(not 1<=abs(z)<=n for c in f for z in c):
        raise ValueError('invalid CNF')
    k=max(2,max((len(set(c)) for c in f),default=0))
    lam=max(1,(max(2,n)-1).bit_length())
    if len(f)<=n*max(1,(lam-1).bit_length()):
        return direct_count(n,f)
    q=threshold(k,n)
    B=4*q**(k-1)
    if stats is None:
        stats=Counter()
    answer=0
    for leaf in leaves(f,q):
        stats['leaves']+=1
        if not leaf:
            answer+=1<<n
            continue
        if any(not c for c in leaf):
            continue
        rows,P=distance_rows(n,len(leaf),B)
        value=count_query(n,leaf,rows)
        for _ in range(3*n):
            best=value
            chosen=None
            for mask in legal_masks(len(leaf),P):
                row=tuple((j,1) for j in range(len(leaf)) if mask>>j&1)
                score=count_query(n,leaf,rows,row)
                stats['trial']+=1
                if score<best:
                    chosen,best=row,score
                if not best:
                    break
            if chosen is None:
                break
            rows.append(chosen)
            value=best
            if not value:
                break
        answer+=value
    return answer
