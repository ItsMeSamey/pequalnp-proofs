"""One-sided arbitrary-form query on a cographic host with rank-one boundary charges."""
from itertools import combinations
from random import SystemRandom


class BinaryField:
    def __init__(self,k):
        # Exhaustive irreducibility by trial division. The chosen field size is O(n).
        for poly in range((1<<k)|1,1<<(k+1),2):
            def divides(d):
                v=poly
                while v.bit_length()>=d.bit_length():v^=d<<(v.bit_length()-d.bit_length())
                return v==0
            if not any(divides(d) for d in range(3,1<<(k//2+1),2)):
                self.poly=poly;self.q=1<<k;break
        else:raise ValueError("no irreducible polynomial")
    def mul(self,a,b):
        out=0
        while b:
            if b&1:out^=a
            b>>=1;a<<=1
            if a&self.q:a^=self.poly
        return out
    def inv(self,a):
        if not a:raise ZeroDivisionError()
        n=self.q-2;out=1
        while n:
            if n&1:out=self.mul(out,a)
            a=self.mul(a,a);n>>=1
        return out
    def det(self,A):
        val=1
        for i in range(len(A)):
            j=next((j for j in range(i,len(A)) if A[j][i]),None)
            if j is None:return 0
            A[i],A[j]=A[j],A[i];pivot=A[i][i]
            val=self.mul(val,pivot);inverse=self.inv(pivot)
            for j in range(i+1,len(A)):
                if not A[j][i]:continue
                scale=self.mul(A[j][i],inverse)
                for k in range(i+1,len(A)):A[j][k]^=self.mul(scale,A[i][k])
        return val


def toggle(s,key):
    if key in s:s.remove(key)
    else:s.add(key)


def evaluate(n,edges,weights,H,charged,b,field):
    if n<3:return 0
    lap=[[0]*n for _ in range(n)]
    for (u,v),x in zip(edges,weights):
        lap[u][u]^=x;lap[v][v]^=x;lap[u][v]^=x;lap[v][u]^=x
    products=set()
    def term(left,right):
        if b in left or b in right or left[0]==left[1] or right[0]==right[1]:return
        key=tuple(sorted((tuple(sorted(left)),tuple(sorted(right)))))
        toggle(products,key)
    pairs=list(combinations(charged,2))
    for u,v in H:
        term((u,v),(u,v))
        for x in charged:
            term((u,v),(x,u));term((u,v),(x,v))
        for xy in pairs:term((u,v),xy)
    result=0
    for (u,v),(x,y) in products:
        rows=[i for i in range(n) if i not in (b,u,v)]
        cols=[i for i in range(n) if i not in (b,x,y)]
        result^=field.det([[lap[i][j] for j in cols] for i in rows])
    return result


def query(n,edges,omega,trials=1,rng=None):
    """Return a verified pair, or None for an unsuccessful search. Default fresh weights."""
    edges=tuple(tuple(e) for e in edges);omega=tuple(tuple(p) for p in omega)
    if n<1 or trials<1:raise ValueError("invalid input")
    charge=[0]*n;neighbors=[[] for _ in range(n)]
    for a,b,t in edges:
        if not (0<=a<n and 0<=b<n and 0<=t<4):raise ValueError("invalid edge")
        charge[a]^=t;charge[b]^=t;neighbors[a].append(b);neighbors[b].append(a)
    seen={0};order=[0]
    for a in order:
        for b in neighbors[a]:
            if b not in seen:seen.add(b);order.append(b)
    if len(seen)!=n:raise ValueError("connected host required")
    if len(set(charge)-{0})>1:raise ValueError("boundary charge rank exceeds one")
    charged={v for v,t in enumerate(charge) if t}
    H=set()
    for i,j in omega:
        if not 0<=i<j<len(edges):raise ValueError("invalid exterior coordinate")
        for u in edges[i][:2]:
            for v in edges[j][:2]:
                if u!=v:toggle(H,tuple(sorted((u,v))))
    if n<3 or not H:return None
    field=BinaryField((2*n).bit_length())
    rng=SystemRandom() if rng is None else rng
    for _ in range(trials):
        weights=[rng.randrange(field.q) for e in edges]
        classes=list(range(n));selected=[]
        def value(first):
            ren={v:j for j,v in enumerate(sorted(set(classes)))}
            m=[ren[v] for v in classes];h=set();charges=set()
            for u,v in H:
                if m[u]!=m[v]:toggle(h,tuple(sorted((m[u],m[v]))))
            for x in charged:toggle(charges,m[x])
            return evaluate(len(ren),[(m[u],m[v]) for u,v,t in edges[first:]],
                            weights[first:],h,charges,m[0],field)
        if not value(0):continue
        for i,(u,v,t) in enumerate(edges):
            if value(i+1):continue
            a,c=classes[u],classes[v]
            if a==c or not weights[i]:raise AssertionError("forced zero contribution")
            classes=[a if z==c else z for z in classes];selected.append(i)
        blocks=sorted(set(classes)-{classes[0]})
        if len(blocks)!=2 or len(selected)!=n-3:raise AssertionError("not a spanning three-forest")
        for block in (*blocks,classes[0]):
            if sum(classes[v]==block for v in charged)%2:raise AssertionError("nonneutral")
        words=[sum(((classes[u]==block)^(classes[v]==block))<<i
                   for i,(u,v,_) in enumerate(edges)) for block in blocks]
        a,c=words
        if not sum((((a>>i)&(c>>j))^((a>>j)&(c>>i)))&1 for i,j in omega)%2:
            raise AssertionError("query witness failed")
        return a,c,tuple(selected)
    return None
