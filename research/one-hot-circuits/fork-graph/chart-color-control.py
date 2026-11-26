"""Independent small-plane controls for the chart-tagged coordinate encoder."""
from collections import defaultdict, Counter
from itertools import product

def field(p, poly):
    n=len(poly)
    q=p**n
    def digits(a):
        return [(a//p**i)%p for i in range(n)]
    def pack(a):
        return sum((x%p)*p**i for i,x in enumerate(a))
    def plus(a,b):
        return pack([x+y for x,y in zip(digits(a),digits(b))])
    def times(a,b):
        u=digits(a);v=digits(b);w=[0]*(2*n-1)
        for i,x in enumerate(u):
            for j,y in enumerate(v):w[i+j]+=x*y
        for i in range(2*n-2,n-1,-1):
            for j,c in enumerate(poly):w[i-n+j]-=w[i]*c
        return pack(w[:n])
    assert all(len({times(a,b) for b in range(q)})==q for a in range(1,q))
    return q,plus,times

def check(p,poly):
    q,add,mul=field(p,poly)
    labels=[(0,x,y) for x,y in product(range(q),repeat=2)]
    labels += [(1,x,1) for x in range(q)]+[(2,1,0)]
    def dot(a,b):
        def coords(a):
            t,x,y=a
            return ((x,y,1),(x,1,0),(1,0,0))[t]
        value=0
        for left,right in zip(coords(a),coords(b)):
            value=add(value,mul(left,right))
        return value
    bins=[defaultdict(list),defaultdict(list)]
    for a in labels:
        for j in range(2):bins[j][(a[0],a[j+1])].append(a)
    endpoint=[{},{}]
    for j in range(2):
        for key,group in bins[j].items():
            color={}
            for start in group:
                if start in color:continue
                color[start]=0; stack=[start]
                while stack:
                    a=stack.pop()
                    for b in group:
                        if a==b or dot(a,b):continue
                        if b in color:assert color[b]!=color[a]
                        else:color[b]=1-color[a];stack.append(b)
            for a in group:endpoint[j][a]=(key,color[a])
    hist=Counter()
    for a,b in product(labels,repeat=2):
        points={a,b}
        ep=[{ei[z] for z in points} for ei in endpoint]
        count=sum(map(len,ep));hist[count]+=1
        out= a==b and dot(a,a)==0
        if count==4:
            bins_by_shore=[sorted(key for key,_ in grp) for grp in ep]
            # The two tagged x and y lists share the same order by chart.
            # Within a chart only the coordinate products are used.
            (t,x),(u,v)=bins_by_shore[0]
            (t1,y),(u1,w)=bins_by_shore[1]
            assert (t,u)==(t1,u1)
            out|=add(add(mul(x,v),mul(y,w)),int(t==u==0))==0
        assert out==(dot(a,b)==0),(q,a,b)
    return q,len(labels),dict(sorted(hist.items())),sum(len(set(e.values())) for e in endpoint)

if __name__=='__main__':
    for args in [(2,[0]),(3,[0]),(2,[1,1]),(5,[0]),(7,[0]),(2,[1,1,0]),(3,[1,0]),(11,[0])]:
        print(*check(*args))
