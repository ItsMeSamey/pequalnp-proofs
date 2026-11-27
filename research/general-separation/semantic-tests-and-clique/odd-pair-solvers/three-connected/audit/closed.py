"""Independent row-neighborhood completion of the even closed-root cases."""
from itertools import combinations
from collections import Counter

def solve(a,b,c):
    n=2+a+b+c
    groups=[set(range(2,2+a)),set(range(2+a,2+a+b)),set(range(2+a+b,n))]
    A,B,C=groups
    allv=set(range(n))
    nb=[set() for _ in allv]
    def add(i,j):
        nb[i].add(j); nb[j].add(i)
    for i in A|C: add(0,i)
    for i in B|C: add(1,i)
    for i in A:
        for j in B: add(i,j)
    counts=Counter()
    def visit(i):
        if i==n:
            counts['allodd']+=1
            for size in range(2,n,2):
                for extras in combinations(range(2,n),size-2):
                    sel={0,1,*extras}
                    if all(len(nb[v]&sel)%2 for v in sel):return
            counts['minimal']+=1
            for x,y in combinations(range(n),2):
                remain=allv-{x,y}
                seen={min(remain)}
                while True:
                    nxt=(set.union(*(nb[j] for j in seen))&remain)|seen
                    if seen==nxt:break
                    seen=nxt
                if seen!=remain:return
            counts['three']+=1
            return
        choices=[j for j in range(i+1,n) if j not in nb[i] and len(nb[j])<5]
        for final in (3,5):
            k=final-len(nb[i])
            if not 0<=k<=len(choices):continue
            for js in combinations(choices,k):
                for j in js:add(i,j)
                visit(i+1)
                for j in js:nb[i].remove(j);nb[j].remove(i)
    visit(2)
    return dict(counts)

for params in [(1,1,2),(1,3,2),(3,3,2),(1,1,4)]:
    print(params,solve(*params),flush=True)
