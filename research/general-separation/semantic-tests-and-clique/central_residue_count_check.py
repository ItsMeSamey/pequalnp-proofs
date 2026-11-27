"""Brute-force controls for central weight residues and signed correction."""
from collections import Counter
from itertools import combinations
from random import Random

rng=Random(23531)
def affine(f,x):
    return (f[0]&x).bit_count()%2^f[1]

def independent(forms):
    span={0}
    for v,_ in forms:
        if v in span:return False
        span|={x^v for x in span}
    return True

def block(q,m):
    forms=[]
    while len(forms)<m:
        f=(rng.randrange(1,1<<q),rng.randrange(2))
        if independent(forms+[f]):forms.append(f)
    return forms

def bits(forms,x):
    return sum(affine(f,x)<<i for i,f in enumerate(forms))

def decode(a,m,M):
    low=sum((sum(all(a>>i&1 for i in c) for c in combinations(range(m),1<<j))%2)<<j
            for j in range(M.bit_length()-1))
    assert low==a.bit_count()%M
    B=m//2-M//2
    return B+(low-B)%M

def exceptions(forms,q,M):
    m=len(forms)
    basis=forms.copy()
    for i in range(q):
        if independent(basis+[(1<<i,0)]):basis.append((1<<i,0))
    inv={bits(basis,x):x for x in range(1<<q)}
    assert len(inv)==1<<q and len(basis)==q
    for w in range(m+1):
        if m//2-M//2<=w<m//2+M//2:continue
        for c in combinations(range(m),w):
            low=sum(1<<i for i in c)
            for z in range(1<<(q-m)):yield inv[(z<<m)|low]

def gen(v,q):
    r=Random(v[0]*(q+1)+v[1])
    def form():return (r.randrange(1<<q),r.randrange(2))
    return [[[form() for _ in range(r.randrange(1,4))] for _ in range(3)] for _ in range(1+r.randrange(2))]

def main(q,M,rare):
    a=block(q,q//2)
    fs=[a,block(q,q-q//2),list(reversed(a)),block(q,q-q//2)]
    exc=[set(exceptions(f,q,M)) for f in fs]
    target=min(exc[0])
    def weights(x):
        return [bits(f,x).bit_count() for f in fs]
    def pair(ws):return (ws[0]+ws[1],ws[2]+ws[3])
    goal=pair(weights(target))
    def root(v,x):
        if rare:return x==target and v==goal
        return all(sum(all(affine(f,x) for f in term) for term in eq)%2==0 for eq in gen(v,q))
    rows={}
    calls=Counter()
    changed=Counter()
    for x in range(1<<q):
        ws=weights(x)
        es=[decode(bits(f,x),len(f),M) for f in fs]
        assert [j for j,s in enumerate(exc) if x in s]==[j for j in range(4) if ws[j]!=es[j]]
        v=pair(es)
        rows[x]=(root(pair(ws),x),root(v,x))
        calls[v]+=rows[x][1]
    seen=set()
    for e in exc:
        for x in e:
            if x not in seen:
                t,s=rows[x]
                changed[int(t)-int(s)]+=1
                seen.add(x)
    direct=sum(t for t,s in rows.values())
    assert sum(calls.values())+changed[1]-changed[-1]==direct
    assert sum(map(len,exc))>len(seen)
    if rare:assert direct==1
    return changed
counts=Counter()
for q,M in [(8,2),(9,2),(10,4)]:
    for rare in (False,True):counts.update(main(q,M,rare))
assert counts[1] and counts[-1]
print('6 cases; positive and negative corrections:',counts[1],counts[-1])
