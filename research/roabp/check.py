from random import Random

def det(rows,s):
    pivots={}
    for i,r in enumerate(rows):
        if s>>i&1:
            v=r&s
            while v:
                k=v.bit_length()
                if k not in pivots:
                    pivots[k]=v
                    break
                v ^= pivots[k]
            else:return 0
    return 1

def check(rows):
    n=len(rows)
    A=list(rows)+[1]
    A[0]|=1<<n
    for S in range(0,1<<n,2):
        count=0
        for x in range(1<<(n+1)):
            if x.bit_count()%2==0 or x&1:continue
            if x&((1<<n)-1)&~S:continue
            if any((x&r).bit_count()%2 for i,r in enumerate(A) if S>>i&1):continue
            count+=1
        assert count%2==det(A,S)

rng=Random(6201)
for n in range(2,9):
    for trial in range(30):
        A=[0]*n
        for i in range(n):
            for j in range(i):
                if rng.randrange(2):
                    A[i]|=1<<j
                    A[j]|=1<<i
        check(A)
print('210 graph formulas checked coefficient by coefficient.')
