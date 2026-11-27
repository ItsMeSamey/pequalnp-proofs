"""Bounded GF4 boundary-relation DP checked against all principal determinants."""
from collections import Counter
from functools import reduce
from itertools import product
from operator import xor
from random import Random
from quaternary_support_check import base, omega, times, minors


def add(*columns):
    return tuple(reduce(xor, row, 0) for row in zip(*columns))


def dot(a,b):
    return reduce(xor,(times[v][w] for v,w in zip(a,b)),0)


def words(k):
    return product(base,repeat=k)


class Boundary:
    def __init__(self,M,I):
        self.I=I
        coords={(0,)*len(I):()}
        self.cols=[]
        for j in range(len(M)):
            if j in I:continue
            c=tuple(M[i][j] for i in I)
            if c in coords:continue
            self.cols.append(c)
            coords={add(v,tuple(times[s][x] for x in c)):old+(s,)
                    for v,old in coords.items() for s in base}
        self.coords=coords
        self.rank=len(self.cols)


def leaf(M,B,selected):
    i=B.I[0]
    zero=(0,)*B.rank
    entries=set()
    invisible=0
    for h in words(B.rank):
        for x in base if selected else (0,):
            col=tuple(c[0] for c in B.cols)
            if selected and times[M[i][i]][x]^dot(col,h):continue
            p=tuple(times[x][a] for a in col)
            entries.add((h,p))
            if h==zero and p==zero:invisible+=1
    return frozenset(entries),invisible>1


class Join:
    def __init__(self,M,P,L,R):
        groups=(L,R)
        self.P=P
        self.L=L
        self.R=R
        self.T=[tuple(B.coords[tuple(v[P.I.index(i)] for i in B.I)] for v in P.cols)
                for B in groups]
        left_coords=[L.coords[tuple(M[i][j] for i in L.I)] for j in R.I]
        self.D=[R.coords[tuple(v[k] for v in left_coords)] for k in range(L.rank)]

    def __call__(self,left,right):
        lr,lg=left
        rr,rg=right
        pzero=(0,)*self.P.rank
        rel=set()
        zero_fiber=0
        TL,TR=self.T
        for pl in words(self.L.rank):
            dl=tuple(dot(pl,[row[j] for row in self.D]) for j in range(self.R.rank))
            for pr in words(self.R.rank):
                dr=tuple(dot(row,pr) for row in self.D)
                p=tuple(dot(col,pl)^dot(other,pr) for col,other in zip(TL,TR))
                for h in words(self.P.rank):
                    hl=tuple(dot(h,[col[j] for col in TL])^dr[j] for j in range(self.L.rank))
                    hr=tuple(dot(h,[col[j] for col in TR])^dl[j] for j in range(self.R.rank))
                    if (hl,pl) in lr and (hr,pr) in rr:
                        rel.add((h,p))
                        if h==pzero and p==pzero:zero_fiber+=1
        return frozenset(rel),bool(lg or rg or zero_fiber>1)


def counts(A,B):
    matrices=(A,B)
    def tree(I):
        bounds=[Boundary(M,I) for M in matrices]
        if len(I)==1:
            hist=Counter(tuple(leaf(M,b,sel) for M,b in zip(matrices,bounds)) for sel in (False,True))
            return bounds,hist
        mid=len(I)//2
        L,left=tree(I[:mid])
        R,right=tree(I[mid:])
        joins=[Join(M,p,l,r) for M,p,l,r in zip(matrices,bounds,L,R)]
        hist=Counter()
        for ls,lc in left.items():
            for rs,rc in right.items():
                key=tuple(j(a,b) for j,a,b in zip(joins,ls,rs))
                hist[key]+=lc*rc
        return bounds,hist
    if not A:return Counter({(True,True):1})
    _,hist=tree(tuple(range(len(A))))
    result=Counter()
    for states,c in hist.items():
        assert all(rel=={((),())} for rel,g in states)
        result[tuple(not g for rel,g in states)]+=c
    return result


def verify(A,B):
    actual=Counter((bool(a),bool(b)) for a,b in zip(minors(A),minors(B)))
    assert counts(A,B)==actual
    return actual


if __name__=='__main__':
    rng=Random(553)
    for n in range(6):
        for _ in range(6):
            mtx=[]
            for _ in range(2):
                M=[[0]*n for _ in range(n)]
                for i in range(n):
                    for j in range(i,n):M[i][j]=M[j][i]=rng.choice(base)
                mtx.append(M)
            verify(*mtx)
    for n in (2,3,4):
        for _ in range(5):
            H=[[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i,n):H[i][j]=H[j][i]=rng.randrange(2)
            a,b=rng.randrange(1<<n),rng.randrange(1<<n)
            A=[[v^(omega if b>>i&b>>j&1 else 0) for j,v in enumerate(row)] for i,row in enumerate(H)]
            B=[[v^(a>>i&a>>j&1) for j,v in enumerate(row)] for i,row in enumerate(A)]
            verify(A,B)
    # No leaf has an invisible null vector, but gluing creates one in the full minor.
    M=[[1,1],[1,1]]
    P,L,R=(Boundary(M,I) for I in ((0,1),(0,),(1,)))
    sl,sr=leaf(M,L,True),leaf(M,R,True)
    assert not sl[1] and not sr[1] and Join(M,P,L,R)(sl,sr)[1]
    # A complete graph with unit edges and zero diagonal is singular at odd order.
    n=6
    A=[[int(i!=j) for j in range(n)] for i in range(n)]
    Z=[[0]*n for i in range(n)]
    d=verify(A,Z)
    assert d[True,False]==31 and d[False,True]==0
    print('36 general GF4 pairs; 15 native updates; six-vertex complete and zero boundary control passed')
