from itertools import product
def build(d):
    if d<2:raise ValueError('use the one-coordinate singleton detector')
    odd=d%2
    rails=6 if odd else 4
    ones={0,3} if odd else {0}
    later=[(0,4,3),(1,3,5)] if odd else [(1,0,3)]
    k=d-len(later)
    vertices=[0]+list(range(rails,rails+k-1))+[1]
    ones.update(vertices[2:-1:2])
    private=rails+k-1
    early=[];middle=[]
    for i in range(k):
        a,b=vertices[i:i+2]
        # At an even-indexed edge in 0-based numbering, a initially carries one.
        # At an odd-indexed edge, a initially carries zero; after both flips a carries one.
        entry=(i,(a,b,private+i))
        (early if i%2==0 else middle).append(entry)
    return ones,early+middle+[(k+i,t)for i,t in enumerate(later)]
def preserved(ones,ops,w):
    value=set(ones)
    for i,g in ops:
        val=w[i]
        old=value.intersection(g)
        value.difference_update(g)
        value.update(g[(g.index(j)+val)%3]for j in old)
    return ones==value
for n in range(2,9):
    x,ops=build(n)
    outcomes=[w for w in product(range(3),repeat=n)if preserved(x,ops,w)]
    assert outcomes==[(0,)*n,(1,)*n]
    print(n,3**n,'complete words')
