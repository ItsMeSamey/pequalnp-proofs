"""Implicit entries for the two-stage RS coset construction."""
def rem(a,b):
    while a.bit_length()>=b.bit_length(): a^=b<<(a.bit_length()-b.bit_length())
    return a

class Network:
    def __init__(self,h,*,max_q=64):
        if h<2 or h%2: raise ValueError('even h>=2 required')
        self.h=h
        self.Q=Q=1<<h
        if Q>max_q: raise ValueError('field cap')
        self.B=B=1<<(h//2)
        self.K=Q//2
        self.mod=next(p for p in range(Q+1,2*Q,2)
                      if all(rem(p,d) for d in range(2,1<<(h//2+1))))
        self.U=tuple(range(B))
        self.reps=tuple(range(0,Q,B))
        s=[1]
        for u in self.U: s=self.product(s,[u,1])
        self.s=tuple(s)
        self.constants=tuple(self.eval(s,t) for t in self.reps)
        powers=[[1]]
        for _ in range(1,B//2): powers.append(self.product(powers[-1],s))
        self.polys=tuple(tuple([0]*b+powers[j]) for j in range(B//2) for b in range(B))
        span=[0]
        generators=[]
        for _ in range(h):
            a=next(x for x in range(1<<(4*h)) if all((x^v).bit_count()>=h//2 for v in span))
            generators.append(a)
            span.extend([a^v for v in span])
        active=[i for i in range(4*h) if any(g>>i&1 for g in generators)]
        self.inner=tuple(sum((g>>i&1)<<j for j,i in enumerate(active)) for g in generators)
        self.ell=len(active)

    def mul(self,a,b):
        z=0
        while b:
            if b&1: z^=a
            b>>=1
            a<<=1
            if a&self.Q: a^=self.mod
        return z

    def product(self,a,b):
        out=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): out[i+j]^=self.mul(x,y)
        return out

    def eval(self,c,x):
        y=0
        for a in reversed(c): y=self.mul(y,x)^a
        return y

    def valid(self,c,n):
        return len(c)==n and all(isinstance(x,int) and 0<=x<self.Q for x in c)

    def first_entry(self,inputs,outputs):
        return int(self.valid(inputs,self.B//2) and self.valid(outputs,self.B) and
                   all(self.eval(inputs,x)==y for x,y in zip(self.constants,outputs)))

    def second_entry(self,site,inputs,outputs):
        if not 0<=site<self.B: raise ValueError('bad coset')
        return int(self.valid(inputs,self.B) and self.valid(outputs,self.B) and
                   all(self.eval(inputs,self.reps[site]^x)==outputs[x] for x in self.U))

    def encode(self,x):
        v=0
        for j,g in enumerate(self.inner):
            if x>>j&1: v^=g
        return v

    def inner_entry(self,x,y):
        return int(0<=x<self.Q and y==self.encode(x))

    def monomial(self,c):
        if not self.valid(c,self.K): raise ValueError('invalid seeds')
        out=[0]*self.K
        for a,p in zip(c,self.polys):
            for j,d in enumerate(p): out[j]^=self.mul(a,d)
        return tuple(out)

    def stages(self,c):
        if not self.valid(c,self.K): raise ValueError('invalid seeds')
        f=[[self.eval(c[b::self.B],v) for v in self.constants] for b in self.U]
        return tuple(self.eval([f[b][i] for b in self.U],t^u)
                     for i,t in enumerate(self.reps) for u in self.U)

    def certificate(self):
        if any(len(p)!=j+1 or p[-1]!=1 for j,p in enumerate(self.polys)): return False
        if any(self.eval(self.s,t^u)!=v for t,v in zip(self.reps,self.constants) for u in self.U): return False
        for j in range(self.K):
            for bit in range(self.h):
                c=[0]*self.K
                c[j]=1<<bit
                p=self.monomial(c)
                if self.stages(c)!=tuple(self.eval(p,x) for x in range(self.Q)): return False
        return True

    def raw_witness(self,c,residual):
        """Return original monomial seeds, unique XOR-chain wires and checked physical CNF."""
        p=self.monomial(c)
        r=self.h*self.K
        raw=sum(a<<(self.h*j) for j,a in enumerate(p))
        n=r
        rows=[]
        outputs=[]
        # Precompute coordinate linear forms in the original monomial seed order.
        columns=[]
        for j in range(r):
            basis=[0]*self.K
            basis[j//self.h]=1<<(j%self.h)
            columns.append([self.encode(self.eval(basis,x)) for x in range(self.Q)])
        for x in range(self.Q):
            for t in range(self.ell):
                inputs=[j+1 for j,col in enumerate(columns) if col[x]>>t&1]
                cur=inputs[0]
                for other in inputs[1:]:
                    n+=1
                    b=((raw>>(cur-1))^(raw>>(other-1)))&1
                    raw|=b<<(n-1)
                    for s in range(8):
                        if s.bit_count()%2:
                            rows.append(tuple(-v if s>>i&1 else v for i,v in enumerate((cur,other,n))))
                    cur=n
                if len(inputs)==1:
                    n+=1
                    raw|=((raw>>(cur-1))&1)<<(n-1)
                    rows.extend([(-cur,n),(cur,-n)])
                    cur=n
                outputs.append(cur)
        for row in residual:
            if any(not 1<=abs(l)<=len(outputs) for l in row): raise ValueError('bad output literal')
            rows.append(tuple(outputs[abs(l)-1]*(1 if l>0 else -1) for l in row))
        ok=all(any(bool(raw>>(abs(l)-1)&1)==(l>0) for l in row) for row in rows)
        return dict(n=n,clauses=tuple(rows),word=raw,outputs=tuple(outputs),accepted=ok,monomial=p)
