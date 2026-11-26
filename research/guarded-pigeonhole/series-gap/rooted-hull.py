"""Compare affine model hull and ordinary PC (no opposite weight axiom supplied)."""
from pathlib import Path
import runpy,sys
from collections import deque
from functools import lru_cache
from itertools import combinations

@lru_cache(None)
def ring(n,d):
    mons=[sum(1<<i for i in a) for k in range(d+1) for a in combinations(range(n),k)]
    index={m:i for i,m in enumerate(mons)}
    low=sum(m.bit_count()<d for m in mons)
    images=[[1<<index[m|1<<v] for m in mons[:low]] for v in range(n)]
    return index,low,images

def insert(x,b):
    while x and x.bit_length() in b:x ^= b[x.bit_length()]
    if not x:return False
    b[x.bit_length()]=x;return True

def reduce(x,b):
    while x and x.bit_length() in b:x^=b[x.bit_length()]
    return x

def null(rows,n):
    b={}
    for x in rows:insert(x,b)
    for p in range(n):
        if p+1 in b:continue
        y=1<<p
        for i in sorted(b):
            if (y&b[i]).bit_count()%2:y|=1<<(i-1)
        yield y

def forms(n,eqs):
    # Form encoding: bit zero is the constant; bit i+1 is free variable i.
    coeff={};rhs={}
    for row,val in eqs:
        while row and row.bit_length() in coeff:
            k=row.bit_length();row^=coeff[k];val^=rhs[k]
        if row:
            k=row.bit_length();coeff[k]=row;rhs[k]=val
        else:assert not val
    out=[0]*n;k=0
    for i in range(n):
        if i+1 not in coeff:k+=1;out[i]=1<<k;continue
        form=rhs[i+1];rest=coeff[i+1]^(1<<i)
        while rest:
            b=rest&-rest;rest^=b;form^=out[b.bit_length()-1]
        out[i]=form
    return k,out

def xor_forms(mask,forms):
    term=0
    while mask:
        b=mask&-mask;mask ^= b
        term ^= forms[b.bit_length()-1]
    return term

def mul(p,images):
    out=0
    while p:
        b=p&-p;p^=b;out^=images[b.bit_length()-1]
    return out

def affine_closure(n,guardpairs,degree,expected):
    idx,low,images=ring(n,degree)
    todo=deque()
    for a,b in guardpairs:
        g=0
        for i in range(n+1):
            if not a>>i&1:continue
            for j in range(n+1):
                if b>>j&1:g^=1<<idx[((1<<i)>>1)|((1<<j)>>1)]
        todo.append(g)
    basis={};affine={};last=len(expected)
    if not expected:return {},0
    while todo:
        p=reduce(todo.popleft(),basis)
        if not p:continue
        j=p.bit_length();basis[j]=p
        if j<=n+1:
            insert(p,affine)
            if len(affine)==last:return affine,len(basis)
        if j<=low:
            for mult in images:todo.append(mul(p,mult))
    return affine,len(basis)

def model_hull(left,neighbors,eqs,subforms,free):
    # A right fiber is a linear system, including mixed equations with p fixed.
    n=left+len(neighbors);m=len(neighbors);span={};total=0
    freepos=[i for i,w in enumerate(subforms) if w>=2 and w.bit_count()==1]
    projected=[None]*free
    for i in freepos:projected[subforms[i].bit_length()-2]=i
    assert None not in projected
    def proj(x):return sum((x>>j&1)<<i for i,j in enumerate(projected))
    for p in range(1<<left):
        rows=[]
        for q,r in eqs:rows.append(((q>>left)<<1)|(r^((q&p).bit_count()%2)))
        for i in range(left):
            if p>>i&1:rows.append(sum((v>>i&1)<<(1+j) for j,v in enumerate(neighbors)))
        for j,v in enumerate(neighbors):
            if (v&p).bit_count()%2:rows.append(1<<(1+j))
        basis={}
        for row in rows:insert(row,basis)
        if 1 in basis:continue
        point=1
        for j in sorted(basis):
            if (basis[j]&point).bit_count()%2:point ^=1<<(j-1)
        q=point>>1
        insert(1|(proj(p|(q<<left))<<1),span)
        total+=1<<(m-len(basis))
        for delta in null([a>>1 for a in rows],m):
            insert(proj(delta<<left)<<1,span)
    return list(null(span.values(),free+1)),total

def check(left,neighbors,eqs):
    n=left+len(neighbors)
    free,sub=forms(n,eqs)
    expected,total=model_hull(left,neighbors,eqs,sub,free)
    if not total:return None
    guards=[]
    for i in range(left):
        g=sum((v>>i&1)<<(j+left)for j,v in enumerate(neighbors))
        guards.append((sub[i],xor_forms(g,sub)))
    for j,v in enumerate(neighbors):guards.append((sub[left+j],xor_forms(v,sub)))
    for degree in (2,3):
        aff,_=affine_closure(free,guards,degree,expected)
        rem=next((x for x in expected if reduce(x,aff)),None)
        if rem is None:return degree
    return (free,sub,expected,aff,rem,total)

def normalize(left,labels):
    planes=[h for h in range(1,8) if all((h&l).bit_count()%2==0 for l in labels[:left]) and (h&4)]
    assert planes
    for b in planes:
        p=sum((l>>2&1)<<j for j,l in enumerate(labels))
        q=sum(((l&b).bit_count()%2)<<j for j,l in enumerate(labels))
        if not p or not q:continue
        yield [(p,1),(q,1)]

def scan(path,limit):
    counts={}
    for i,line in enumerate(open(path)):
        if i==limit:break
        *l,h=line.split();left=len(l);types=int(h,16);ns=[];labels=list(map(int,l))
        for v in range(1<<(left+2)):
            if types>>v&1:ns.append(v//4);labels.append(v%4)
        for eqs in normalize(left,labels):
            ans=check(left,ns,eqs)
            if isinstance(ans,tuple):
                print('AFFINE GAP',left,ns,eqs,ans,flush=True);return
            counts[ans]=counts.get(ans,0)+1
    print('Counts',counts)
if __name__=='__main__':scan(sys.argv[1],int(sys.argv[2]))
