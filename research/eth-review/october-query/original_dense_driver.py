"""Deterministic disjoint leaf and sparse-hash selector connected to typed counts."""
from collections import Counter
from itertools import combinations,product
from math import isqrt
from hash_query_adapter import count_query
from source_cnf_driver import count as direct_count

def normalize(f):
    clauses=sorted({frozenset(c) for c in f if not any(-z in c for z in c)},
                   key=lambda c:(len(c),sorted(c)))
    keep=[]
    for c in clauses:
        if not any(s<=c for s in keep):keep.append(c)
    return keep

def threshold(k,n):
    lam=max(1,(max(2,n)-1).bit_length())
    den=isqrt(lam-1)+1
    gamma=2*(3**(k-1)-1);q=1<<(gamma-1).bit_length()
    while True:
        C=4*sum((3*q)**j for j in range(k-1))
        if gamma*(4*C*q-1).bit_length()*den<=q:return q
        q*=2

def leaves(f,m):
    stack=[normalize(f)]
    while stack:
        node=stack.pop();freq=Counter()
        for c in node:
            for j in range(1,len(c)):
                for z in combinations(sorted(c),j):freq[len(c),z]+=1
        choices=[(k,-len(z),z) for (k,z),num in freq.items() if num>=m**(k-len(z))]
        if not choices:
            yield [tuple(sorted(c)) for c in node];continue
        k,_,z=min(choices);H=frozenset(z)
        chosen=[c for c in node if len(c)==k and H<=c]
        rest=[c for c in node if c not in chosen]
        stack.append(normalize(rest+[c-H for c in chosen]+[{ -v } for v in H]))
        stack.append(normalize(rest+[H]))

def distance_rows(n,m,B):
    mu=m.bit_length();P=20000*B*B*mu*mu
    if m<=P:return [],P # Every nonzero word already has weight >=m/P.
    d=min(m,320000*B*B*mu**3)
    q=1
    while q*d<m:q*=2
    if q==1:shifts=(0,)*d
    else:
        shifts=next(seq for seq in product(range(q),repeat=d)
              if all(abs(sum(1-2*((v&b).bit_count()&1) for v in seq))*200*B*mu<=d
                  for b in range(1,q)))
    c=(d+8*B-1)//(8*B);h=(d-1)//(100*B*mu)
    def good(mat):
        for j in range(1,h+1):
            for subset in combinations(range(d),j):
                z=sum(1<<i for i in subset)
                if not any((w&z).bit_count()%2 for w in mat):return False
        return True
    for packed in range(1<<(c*d)):
        mat=tuple((packed>>(d*i))&((1<<d)-1) for i in range(c))
        if good(mat):break
    else:raise ArithmeticError('local distance search exhausted')
    rows=[]
    for side in (0,1):
        for u in range(q):
            for mask in mat:
                row=[]
                for j in range(d):
                    idx=(u if side==0 else u^shifts[j])*d+j
                    if idx<m and (mask>>j)&1:row.append((idx,1))
                if row:rows.append(tuple(row))
    assert len(rows)<=3*n
    return rows,P

def leaf_count(n,f,B,stats):
    if not f:return 1<<n
    if any(not c for c in f):return 0
    m=len(f);rows,P=distance_rows(n,m,B)
    value=count_query(n,f,rows)
    for _ in range(3*n):
        best=value; chosen=None
        for j in range(1,min(m,P)+1):
            for ix in combinations(range(m),j):
                row=tuple((i,1) for i in ix)
                candidate=count_query(n,f,rows,row);stats['trial']+=1
                if candidate<best:best=candidate;chosen=row
                if not best:break
            if not best:break
        if chosen is None:break # singletons detect any remaining false assignment
        rows.append(chosen);value=best
        if not value:break
    stats['accepted']+=1
    return count_query(n,f,rows)

def count(n,clauses,stats=None):
    f=[tuple(c) for c in clauses]
    if n<0 or any(not 1<=abs(z)<=n for c in f for z in c):raise ValueError('bad CNF')
    k=max(2,max((len(set(c)) for c in f),default=0))
    lam=max(1,(max(2,n)-1).bit_length());nu=max(1,(lam-1).bit_length())
    if len(f)<=n*nu:return direct_count(n,f)
    q=threshold(k,n);B=4*q**(k-1)
    if stats is None:stats=Counter()
    total=0
    for leaf in leaves(f,q):
        stats['leaves']+=1
        total+=leaf_count(n,leaf,B,stats)
    return total

def witness(n,f):
    f=[tuple(c) for c in f]
    if not count(n,f):return None
    answer=[]
    for i in range(1,n+1):
        if count(n,f+[(-i,)]):f.append((-i,));answer.append(0)
        else:f.append((i,));answer.append(1)
    return tuple(answer)
