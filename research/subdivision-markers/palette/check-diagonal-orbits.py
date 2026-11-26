from itertools import combinations,product,permutations

def rank(cols):
    P={}
    for x in cols:
        while x and x.bit_length() in P:x^=P[x.bit_length()]
        if x:P[x.bit_length()]=x
    return len(P)

def wedge(cols,r):
    vals=[]
    for I in combinations(range(r),len(cols)):
        mask=sum(1<<i for i in I)
        vals.append(int(rank([v&mask for v in cols])==len(cols)))
    return tuple(i for i,b in enumerate(vals) if b)

def diagonal(w,d):
    return sum(1<<(((i*d+j)*d+k)*d+l) for i,j,k,l in product(w,repeat=4))

def insert(Z,x):
    while x and x.bit_length() in Z:x^=Z[x.bit_length()]
    if not x:return False
    Z[x.bit_length()]=x
    return True

n=6
edges=list(combinations(range(n),2))
def V(edge):
    i,j=edge
    return ((1<<i)|(1<<j)) & ((1<<(n-1))-1)
def diag(S):
    return diagonal(wedge([V(e) for e in S],n-1),10)

# Canonical stars for component sizes 4+1+1, 3+2+1, 2+2+2.
seeds=[[(0,1),(0,2),(0,3)],[(0,1),(0,2),(3,4)],[(0,1),(2,3),(4,5)]]
def act(S,i):
    def f(x):
        if x==i:return i+1
        if x==i+1:return i
        return x
    return [tuple(sorted(map(f,e))) for e in S]
Z={}; Q=[]
def add(S):
    if insert(Z,diag(S)):Q.append(S)
for S in seeds:add(S)
k=0
while k<len(Q):
    S=Q[k];k+=1
    for i in range(n-1):add(act(S,i))
allsets=[S for S in combinations(edges,3) if rank([V(e) for e in S])==3]
for S in allsets:
    z=diag(S)
    while z and z.bit_length() in Z:z^=Z[z.bit_length()]
    assert z==0
assert all(rank([V(e) for e in S])==3 for S in Q)
assert all(diagonal(wedge(list(S),4),6)!=diagonal(wedge([3,12],4),6) for S in combinations([1,2,4,8],2))
print(len(allsets),'K6 forests covered from three flat seeds;',len(Q),'physical representatives')
