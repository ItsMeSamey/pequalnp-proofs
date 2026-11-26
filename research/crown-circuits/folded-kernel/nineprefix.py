from itertools import product
G=[]
def gate(o,a,b):
    G.append((o,a,b))
    return 23+len(G)
def add(x,y):return gate(0,x,y)
def mul(x,y):return gate(1,x,y)
def three(x,y,z):
    xy=add(x,y)
    return add(mul(x,y),mul(xy,z)),xy
z=[add(i,i+12) for i in range(9)]
rows=[add(add(z[a],z[a+1]),z[a+2]) for a in [0,3,6]]
cols=[add(add(z[b],z[b+3]),z[b+6]) for b in [0,1,2]]
r,pre=three(*rows)
c,_=three(*cols)
P=add(r,c);U=add(pre,rows[2])
assert len(G)==31
for i,j in product(range(12),repeat=2):
    w=[k in (i,12+j) for k in range(24)]
    for o,a,b in G:w.append(w[a]&w[b] if o else w[a]|w[b])
    assert w[U]==(i<9 or j<9)
    assert w[P]==(i<9 and j<9 and i!=j)
print('31 gates, U and P correct on 144/144 inputs')
