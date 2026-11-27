"""Physical native witness by exact rational paired-row aggregation."""
from fractions import Fraction
from itertools import product

def reduce_row(row, basis):
    row=list(row)
    for i in sorted(basis):
        a=row[i]
        if a:row=[x-a*y for x,y in zip(row,basis[i])]
    return row

def insert(row, basis):
    row=reduce_row(row,basis)
    i=next((j for j,v in enumerate(row) if v),None)
    if i is None:return False
    basis[i]=[Fraction(v,row[i]) for v in row]
    return True

def aggregate(options,d):
    c=[[0]*d for _ in range(d)]
    for _,(a,b) in options:
        for i in range(d):
            for j in range(i+1,d):
                c[i][j]+=a[i]*b[j]-a[j]*b[i]
    for i in range(d):
        for j in range(i):c[i][j]=-c[j][i]
    pivot=next(((i,j) for i in range(d) for j in range(i+1,d) if c[i][j]),None)
    if pivot is None:return 'zero',None
    u,v=pivot
    a=[Fraction(c[i][v],c[u][v]) for i in range(d)];b=c[u]
    if all(c[i][j]==a[i]*b[j]-a[j]*b[i] for i in range(d) for j in range(i+1,d)):
        return 'simple',(a,b)
    return 'branch',None

def prepare(feedback,menus,r,s):
    n=len(menus);N=3*n
    if sorted(feedback)!=list(range(N)) or not (0<=r<N and 0<=s<N):
        raise ValueError('invalid feedback or root')
    if any(not m or any(x not in (0,1,2) for x in m)for m in menus):
        raise ValueError('invalid gate menu')
    if r==s:return []
    forced={};options=[]
    for g,menu in enumerate(menus):
        q=[]
        for x in menu:
            rows=[]
            for i in range(3*g,3*g+3):
                if i==s:continue
                v=[0]*N;v[i]=2;v[feedback[3*g+(i%3+x)%3]]-=1
                del v[r];rows.append(v)
            if not q and len(rows)==3 and not insert(map(sum,zip(*rows)),forced):
                return None
            q.append((x,rows[:2]))
        options.append(q)
    free=[j for j in range(N-1)if j not in forced]
    def project(v):
        v=reduce_row(v,forced)
        return [v[j] for j in free]
    opts=[[(x,tuple(project(v)for v in pair))for x,pair in q] for q in options]
    return opts

def solve(feedback,menus,r,s):
    opts=prepare(feedback,menus,r,s)
    if opts is None:return None
    if not opts:return tuple(m[0] for m in menus)
    n=len(opts);dimension=2*n
    pairs=[None]*n;bad=[];good=[]
    for j,q in enumerate(opts):
        kind,pairs[j]=aggregate(q,dimension)
        if kind=='zero':return None
        (bad if kind=='branch' else good).append(j)
    def independent():
        b={}
        return all(insert(v,b)for pair in pairs for v in pair)
    for choices in product(*(opts[j] for j in bad)):
        witness=[None]*n
        for j,(x,pair)in zip(bad,choices):witness[j]=x;pairs[j]=pair
        if not independent():continue
        for j in good:
            for x,pair in opts[j]:
                pairs[j]=pair
                if independent():witness[j]=x;break
            else:raise AssertionError('nonzero exterior product lost during recovery')
        return tuple(witness)
    return None
