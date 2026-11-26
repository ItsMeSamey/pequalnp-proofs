from itertools import product, combinations
def orders(n):
    for k in range(1,n+1):
        for t in product(range(k),repeat=n):
            if len(set(t))==k:yield t
def extreme(t,C):
    a,b=min(t[i] for i in C),max(t[i] for i in C)
    return {i for i in C if t[i] in (a,b)}
def rank(rows):
    piv={}
    for x in rows:
        while x:
            p=x.bit_length()
            if p not in piv:piv[p]=x;break
            x^=piv[p]
    return len(piv)
def check(n):
    full=set(range(n)); counts=[0,0,0]; width=0
    for a in orders(n):
        if a!=tuple(sorted(a)):continue
        for b in orders(n):
            T=(a,b); rows=[sum(1<<i for i in full if t[i]>=k) for t in T for k in range(max(t)+2)]
            counts[0]+=1
            def quartet(C):
                return not (extreme(a,C)&extreme(b,C))
            bad=False
            for C in combinations(range(n),4):
                if quartet(C):
                    bad=True
                    M=sum(1<<i for i in C)
                    candidates=[(j,x&M) for j,x in enumerate(rows) if (x&M).bit_count() in (1,3)]
                    assert any(x^y^z^w==M for (i,x),(j,y),(k,z),(l,w) in combinations(candidates,4) if i<j<max(a)+2<=k<l)
                    break
            if bad:counts[1]+=1;continue
            counts[2]+=1
            U=set(full); M=(1<<n)-1; F=M; R=set(range(len(rows))); D=set()
            def measure():
                return rank([rows[i]&F for i in D])+rank([rows[i]&(M^F) for i in R])
            while True:
                for i in sorted(R.copy()):
                    if rows[i]&F in (0,F):
                        R.remove(i);D.add(i);width=max(width,measure())
                if not U:break
                e=min(extreme(a,U)&extreme(b,U)); U.remove(e);F^=1<<e
                width=max(width,measure())
            assert width<=4
    return counts,width
for n in range(1,6):print(n,check(n))
