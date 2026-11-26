"""Exact directed-generator merge on source OR/COPY tensors and a true Cauchy packet."""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import prod

MOD = 256


def valuation(a):
    return (a & -a).bit_length()-1


class Generators:
    # Row elimination; the pivot divides every entry in its pivot row.
    def __init__(self, rows):
        rows = [[x % MOD for x in row] for row in rows]
        self.pivots, self.rows = [], []
        while any(any(row) for row in rows):
            _,i,j = min((valuation(x),i,j) for i,row in enumerate(rows)
                        for j,x in enumerate(row) if x)
            base = rows.pop(i)
            p = 1 << valuation(base[j])
            inv = pow(base[j]//p, -1, MOD)
            base = [(x*inv)%MOD for x in base]
            assert all(x % p == 0 for x in base)
            self.rows.append(base)
            self.pivots.append(j)
            rows = [[(a-(row[j]//p)*b)%MOD for a,b in zip(row,base)] for row in rows]

    def coordinates(self, row):
        out = []
        row = [a % MOD for a in row]
        for j,base in zip(self.pivots,self.rows):
            assert row[j] % base[j] == 0
            scale = row[j] // base[j]
            out.append(scale)
            row = [(a-scale*b)%MOD for a,b in zip(row,base)]
        assert not any(row)
        return out


def inds(r, cap):
    if r == 0:
        yield ()
    else:
        for i in range(cap+1):
            for tail in inds(r-1,cap-i):
                yield (i,)+tail


def mul(a,b):
    out=defaultdict(int)
    for s,v in a.items():
        for t,w in b.items():
            k=tuple(i+j for i,j in zip(s,t))
            out[k]=(out[k]+v*w)%MOD
    return {k:v for k,v in out.items() if v}


def plus(*terms):
    out=defaultdict(int)
    for s,a in terms:
        for k,v in a.items():
            out[k]=(out[k]+s*v)%MOD
    return {k:v for k,v in out.items() if v}


def linear(const, coeff):
    d=len(coeff)
    p={(0,)*d:const} if const else {}
    return plus((1,p), (1,{tuple(int(i==j) for j in range(d)):v
                           for i,v in enumerate(coeff) if v}))


def powers(forms, exps, z):
    p={z:1}
    for form,e in zip(forms,exps):
        for _ in range(e):
            p=mul(p,form)
    return p


def raw_kernel(t, zeta):
    L=8
    grid=range(-L,L)
    T=t+2*L*zeta
    norm=prod(-u for u in grid if u)
    W=[]
    for x in range(L):
        row=[]
        for y in range(L):
            w=Fraction(prod(T-u for u in grid if u!=y-x),norm)
            assert w.denominator % 2
            row.append(w.numerator * pow(w.denominator,-1,MOD)%MOD)
        W.append(row)
    pairs=((0,4),(1,6),(2,5),(3,7))
    return [[(row[i]+row[j])%MOD for i,j in pairs] for row in W]


def run(t,zeta):
    w=raw_kernel(t,zeta)
    scopes=[(0,1),(2,3),(4,5),()]
    D=6
    mask=lambda row, keep: [x if j in keep else 0 for j,x in enumerate(row)]

    def gate(g,forms,one):
        if g==3:
            return one
        x,y=forms
        if g==0:
            return plus((1,x),(1,y),(-1,mul(x,y)))
        if g==1:
            return plus((1,one),(-1,x),(1,mul(x,y)))
        return plus((1,one),(-1,x),(-1,y),(2,mul(x,y)))

    def build(ids):
        outside=set(range(4))-set(ids)
        gi=Generators([mask(w[p],outside) for g in ids for p in scopes[g]])
        go=Generators([mask(w[p],ids) for g in outside for p in scopes[g]])
        di=sum(len(scopes[g]) for g in ids)
        db=list(inds(len(go.rows),D-di))
        tab={b:defaultdict(int) for b in db}
        if len(ids)==1:
            g=ids[0]
            for x in (0,1):
                entries=[linear(x*w[p][g],gi.coordinates(mask(w[p],outside))) for p in scopes[g]]
                val=gate(g,entries,{(0,)*len(gi.rows):1})
                for b in db:
                    moment=prod((row[g]*x)**k for row,k in zip(go.rows,b))
                    for a,v in val.items():
                        tab[b][a]=(tab[b][a]+v*moment)%MOD
            return gi,go,tab,di
        mid=len(ids)//2
        aa,bb=ids[:mid],ids[mid:]
        ai,ao,at,da=build(aa)
        bi,bo,bt,dd=build(bb)
        ni,na,nb=map(len,(gi.rows,ao.rows,bo.rows))
        Z=(0,)*(ni+na+nb)
        x=[linear(0, gi.coordinates(mask(s,outside))+[0]*na+bo.coordinates(mask(s,bb))) for s in ai.rows]
        y=[linear(0, gi.coordinates(mask(s,outside))+ao.coordinates(mask(s,aa))+[0]*nb) for s in bi.rows]
        v=[linear(0,[0]*ni+ao.coordinates(mask(s,aa))+bo.coordinates(mask(s,bb))) for s in go.rows]
        for b in db:
            bp=powers(v,b,Z)
            for a1 in inds(len(x),da):
                term=mul(bp,powers(x,a1,Z))
                if not term: continue
                for a2 in inds(len(y),dd):
                    joint=mul(term,powers(y,a2,Z))
                    for key,coeff in joint.items():
                        gamma,ma,mb=key[:ni],key[ni:ni+na],key[ni+na:]
                        tab[b][gamma]=(tab[b][gamma]+coeff*at[ma].get(a1,0)*bt[mb].get(a2,0))%MOD
        return gi,go,tab,di

    _,_,tab,_=build([0,1,2,3])
    expected=0
    for x in product(range(2),repeat=4):
        q=[sum(a*b for a,b in zip(row,x))%MOD for row in w]
        expected+=(q[0]+q[1]-q[0]*q[1])*(1-q[2]+q[2]*q[3])*(1-q[4]-q[5]+2*q[4]*q[5])
    assert tab[()][()]==expected%MOD
    return expected%MOD


if __name__=='__main__':
    samples=[(0,0),(1,0),(-1,0),(1,1),(-3,1),(2,1),(3,3)]
    values=[run(*s) for s in samples]
    print(f"{len(samples)} exact canonical contractions matched modulo {MOD}: {values}")
