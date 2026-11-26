"""Exact small boundary ranks and histogram-to-profile inversion."""
from fractions import Fraction
from collections import Counter
from math import factorial, prod
from itertools import permutations, product


def partitions(n, limit=None):
    if not n:
        yield ()
        return
    for j in range(1,min(n,limit or n)+1):
        for rest in partitions(n-j,j):
            yield (j,)+rest


def lengths(p):
    left=set(range(len(p))); result=[]
    while left:
        i=next(iter(left)); a=0
        while i in left:
            left.remove(i); i=p[i]; a+=1
        result.append(a)
    return tuple(sorted(result,reverse=True))


def content(b):
    ranks=[0]*(b+1)
    for shape in partitions(b):
        coeff=[1]; hooks=1
        for r,row in enumerate(shape):
            for c in range(row):
                t=c-r
                coeff=[x+y for x,y in zip([0]+coeff,[t*a for a in coeff]+[0])]
                hooks*=row-c+sum(j>c for j in shape[r+1:])
        f=factorial(b)//hooks
        for k,z in enumerate(coeff):
            ranks[k]+=bool(z)*f*f
    return ranks


def modular_rank(rows,prime):
    basis={}
    for keyrow in rows:
        row=list(keyrow)
        for j in range(len(row)):
            if not row[j]:
                continue
            if j not in basis:
                inv=pow(row[j],-1,prime)
                basis[j]=[v*inv%prime for v in row[j:]]
                break
            val=row[j]
            for t,v in enumerate(basis[j],j):
                row[t]=(row[t]-val*v)%prime
    return len(basis)


def profile_column(part,d):
    tab=Counter({(0,)*d:1})
    for cycle in part:
        nxt=Counter()
        for hist,w in tab.items():
            for c in range(d):
                h=list(hist); h[c]+=cycle; nxt[tuple(h)]+=w
        tab=nxt
    return tab


def recover(columns,observed):
    basis={}
    for h in sorted(set().union(*columns)):
        row=[Fraction(c[h]) for c in columns]+[Fraction(observed[h])]
        for j in range(len(columns)):
            if not row[j]: continue
            if j not in basis:
                basis[j]=[v/row[j] for v in row]
                break
            val=row[j]
            row=[x-val*y for x,y in zip(row,basis[j])]
        else: assert row[-1]==0
    assert len(basis)==len(columns)
    out=[0]*len(columns)
    for j in reversed(range(len(columns))):
        out[j]=basis[j][-1]-sum(basis[j][i]*out[i] for i in range(j+1,len(columns)))
    return out


def main():
    cases=0
    for n in range(1,6):
        ps=list(permutations(range(n)))
        table=[[len(lengths([q.index(v) for v in p])) for p in ps] for q in ps]
        for k,r in enumerate(content(n)[1:],1):
            # This Mersenne prime exceeds the Hadamard bound for every minor through n=5.
            assert modular_rank(([int(v==k) for v in row] for row in table),2**521-1)==r
            cases+=1
    palette_tests=0
    from itertools import combinations
    for n in range(1,7):
        ps=[(p,lengths(p)) for p in permutations(range(n))]
        for d in range(1,min(3,n)+1):
            for allowed in combinations(range(1,n+1),d):
                parts=[p for p in partitions(n) if set(p)<=set(allowed)]
                if not parts: continue
                # Use a nonuniform positive multiplicity to ensure different coefficient profiles.
                selected=[(p,l,1+sum(i*v for i,v in enumerate(p))%7)
                          for p,l in ps if l in parts]
                hist=Counter(); truth=Counter()
                for p,l,m in selected:
                    truth[l]+=m
                    for coloring in product(range(d),repeat=n):
                        if all(coloring[i]==coloring[v] for i,v in enumerate(p)):
                            hist[tuple(coloring.count(c) for c in range(d))]+=m
                assert recover([profile_column(p,d) for p in parts],hist)==[truth[p] for p in parts]
                palette_tests+=1
    print('exact ranks',cases,'palette inversions',palette_tests)


if __name__=='__main__':
    main()
