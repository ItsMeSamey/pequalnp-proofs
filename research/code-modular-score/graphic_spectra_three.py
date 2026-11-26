from itertools import combinations
from random import Random
from collections import Counter
def space(vectors):
    span={0}
    for v in vectors: span|={x^v for x in span}
    return tuple(sorted(span))
planes=sorted({space([i,j]) for i,j in combinations(range(1,16),2)})
piv={}
for d in range(16):
 for a,b in combinations(range(1,16),2):
    r=sum(1<<i for i,P in enumerate(planes) if d in P and all(x not in P for x in (a,b,a^b)))
    while r:
        j=r.bit_length()-1
        if j not in piv: piv[j]=r;break
        r^=piv[j]
free=set(range(35))-piv.keys()
basis=[]
for v in free:
 r=1<<v
 for j in sorted(piv):
    if (r&piv[j]).bit_count()%2:r^=1<<j
 basis.append(r)
print('rank',len(piv),'weights',sorted(Counter(x.bit_count() for x in space(basis)).items()),flush=True)
def spectra(types):
    outputs=set()
    def visit(i,sums):
        if i==len(types):
            p=space(sums)
            if len(p)==4 and len(sums)==3: outputs.add(p)
            return
        for j in range(len(sums)):
            sums[j]^=types[i]
            visit(i+1,sums)
            sums[j]^=types[i]
        sums.append(types[i]); visit(i+1,sums); sums.pop()
    visit(0,[])
    return outputs
rng=Random(76)
for n in (5,6,7):
    best=(0,None)
    for _ in range(150):
        a=rng.sample(range(1,16),n-1)
        z=0
        for x in a:z^=x
        a.append(z)
        if len(space(a))!=16:continue
        k=len(spectra(a))
        if k>best[0]:best=(k,a.copy())
        if k==35:break
    print('K',n,best,flush=True)
