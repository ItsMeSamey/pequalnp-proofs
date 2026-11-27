"""Enumerate the six-site box and check a direct equality of projected guards."""
from itertools import combinations
from random import Random


def physical_table():
    rows=[0]*6
    for i,j in ((0,2),(1,2),(0,3),(1,4),(1,5)):
        rows[i]|=1<<j
        rows[j]|=1<<i
    c=(1<<0)|(1<<5)
    table={}
    for w in range(64):
        err=c^sum((((r&w).bit_count()%2)<<i) for i,r in enumerate(rows))
        if not(w&err&60):
            table.setdefault((w&3,err&3),w)
    assert set(table)=={(s,f) for s in range(4) for f in range(4)}-{(1,0),(1,2)}
    return rows,c,table


def test():
    rows,local_c,table=physical_table()
    rng=Random(11566); tested=0
    for n in range(1,8):
        for rep in range(3):
            A=[0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    A[i]|=1<<j
                    A[j]|=1<<i
            c=rng.randrange(1<<n)
            # Fixed hub b=0. Keep all exposed occupancies on the same raw sites.
            physical=[0]*(5*n+1)
            for i,r in enumerate(A):
                physical[i]=r
            hub=n
            pc=0
            for i in range(n):
                sites=[i,hub]+list(range(n+1+4*i,n+5+4*i))
                for k,site in enumerate(sites):
                    if (local_c>>k)&1:
                        pc ^= 1<<site
                    for l in range(k):
                        if (rows[k]>>l)&1:
                            dest=sites[l]
                            physical[site]|=1<<dest
                            physical[dest]|=1<<site
                if not(c>>i&1):
                    pc ^= 1<<i
            for x in range(1<<n):
                ok=all(not(x>>i&1) or ((r&x).bit_count()%2==(c>>i&1))
                       for i,r in enumerate(A))
                word=x
                extend=True
                for i,r in enumerate(A):
                    a=(x>>i)&1
                    g=((r&x).bit_count()%2)^((c>>i)&1)^1
                    choices=[v for (s,e),v in table.items() if s==a and (not a or (e&1)==g)]
                    if not choices:
                        extend=False
                        break
                    word |= (choices[0]>>2) << (n+1+4*i)
                assert ok==extend
                if ok:
                    assert (word>>hub&1)==0 and all(not(word>>i&1) or
                       (r&word).bit_count()%2==(pc>>i&1) for i,r in enumerate(physical))
                tested+=1
    print("14 open states;",tested,"projection tests with raw physical lifting")


if __name__=="__main__":
    test()
