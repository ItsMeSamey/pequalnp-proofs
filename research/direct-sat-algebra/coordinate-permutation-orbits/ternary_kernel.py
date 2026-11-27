"""Ternary-block solver. Returns status, actual permutation SLP on YES, and kernel rank."""
from itertools import product
from orbit_subcube import move
def compose(a,b):return tuple(a[i] for i in b)
def inverse(a):
    b=[0]*len(a)
    for i,j in enumerate(a):b[j]=i
    return tuple(b)
def solve(R,F,p,Z,rank_cap=10):
    R,F=tuple(R),tuple(F);D=len(R);I=tuple(range(D))
    if sorted(R)!=list(I) or sorted(F)!=list(I) or min(p,Z)<0 or (p|Z)>>D:raise ValueError('invalid input')
    if move(R,p)!=p or compose(F,F)!=I:return 'outside',None,None
    sw={(i,F[i]) for i in I if i<F[i]};q=list(sw)
    for i,j in q:
        v=tuple(sorted((R[i],R[j])))
        if v not in sw:sw.add(v);q.append(v)
    adj=[[] for _ in I]
    for i,j in sw:adj[i].append(j);adj[j].append(i)
    seen=set();B=[]
    for i in I:
        if i in seen:continue
        q=[i];seen.add(i)
        for j in q:
            for k in adj[j]:
                if k not in seen:seen.add(k);q.append(k)
        if len(q)>3:return 'outside',None,None
        B.append(sorted(q))
    m=len(B);ops=['I','R','F'];perms=[I,R,F]
    def op(i,j=None):
        ops.append(('inv',i) if j is None else ('mul',i,j))
        perms.append(inverse(perms[i]) if j is None else compose(perms[i],perms[j]))
        return len(ops)-1
    def local(i):
        sign=0;offset=[]
        for j,b in enumerate(B):
            y=[b.index(perms[i][x]) for x in b]+list(range(len(b),3))
            offset.append(y[0]);sign|=int((y[1]-y[0])%3==2)<<j
        return sign,offset
    ri=op(1);g=2;H={};kernel=[]
    for _ in range(3*m+1):
        h=g;s,_=local(h)
        while s and s.bit_length() in H:
            t,a=H[s.bit_length()];h=op(op(a),h);s^=t
        if s:H[s.bit_length()]=s,h
        else:kernel.append(h)
        g=op(op(1,g),ri)
    hs=list(H.values())
    for j,(_,a) in enumerate(hs):
        kernel.append(op(a,a))
        for _,b in hs[:j]:kernel.append(op(op(a,b),op(op(a),op(b))))
    K={}
    def reduce(v,id=None):
        v=v[:]
        for i,(w,h) in sorted(K.items()):
            a=v[i]
            if a:
                v=[(x-a*y)%3 for x,y in zip(v,w)]
                if id is not None:id=op(op(h) if a==1 else h,id)
        return v,id
    for h in kernel:
        s,v=local(h);assert s==0
        v,h=reduce(v,h)
        if not any(v):continue
        i=next(j for j,x in enumerate(v) if x)
        if v[i]==2:v=[-x%3 for x in v];h=op(h)
        K[i]=v,h
        for _,g in hs:kernel.append(op(op(g,h),op(g)))
    rank=len(K)
    if rank_cap is not None and rank>rank_cap:return 'cap',None,rank
    # Make the quotient sign action fix a common affine origin.
    cols=[reduce([int(i==j) for i in range(m)])[0] for j in range(m)]
    eq={}
    for s,h in hs:
        rhs=reduce(local(h)[1])[0]
        for i,t in enumerate(rhs):
            v=[2*(s>>j&1)*cols[j][i]%3 for j in range(m)]
            for j,(w,z) in sorted(eq.items()):
                a=v[j];v=[(x-a*y)%3 for x,y in zip(v,w)];t=(t-a*z)%3
            if not any(v):assert t==0;continue
            j=next(j for j,x in enumerate(v) if x);a=v[j];eq[j]=[a*x%3 for x in v],a*t%3
    c=[0]*m
    for j,(v,t) in sorted(eq.items(),reverse=True):c[j]=(t-sum(x*y for x,y in zip(v,c)))%3
    for co in product(range(3),repeat=rank):
        k=[sum(a*v[j] for a,(v,_) in zip(co,K.values()))%3 for j in range(m)]
        eq={};bad=False
        for j,b in enumerate(B):
            allowed=[]
            for s in (0,1):
                pos=[(c[j]+(1-2*s)*(i-c[j])+k[j])%3 for i,x in enumerate(b) if p>>x&1]
                if all(i<len(b) and not Z>>b[i]&1 for i in pos):allowed.append(s)
            if not allowed:bad=True;break
            if len(allowed)==2:continue
            v=sum((s>>j&1)<<i for i,(s,_) in enumerate(hs));t=allowed[0]
            while v and v.bit_length() in eq:
                w,z=eq[v.bit_length()];v^=w;t^=z
            if v:eq[v.bit_length()]=v,t
            elif t:bad=True;break
        if bad:continue
        a=0
        for i,(v,t) in sorted(eq.items()):
            if (a&v).bit_count()%2!=t:a|=1<<(i-1)
        h=0
        for i,(_,g) in enumerate(hs):
            if a>>i&1:h=op(g,h)
        s,b=local(h);delta=[(2*(s>>j&1)*c[j]+k[j]-b[j])%3 for j in range(m)]
        for j,(v,g) in sorted(K.items()):
            a=delta[j]
            if a:delta=[(x-a*y)%3 for x,y in zip(delta,v)];h=op(g if a==1 else op(g),h)
        assert not any(delta) and not move(perms[h],p)&Z
        return 'yes',(ops,h),rank
    return 'no',None,rank
