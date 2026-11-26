from collections import Counter
from itertools import product
from random import Random
class Circuit:
    def __init__(self,n): self.n,self.gates=n,[]
    def gate(self,op,a,b):
        self.gates.append((op,a,b))
        return self.n+len(self.gates)-1
    def reduce(self,op,wires):
        wires=iter(wires)
        out=next(wires)
        for w in wires: out=self.gate(op,out,w)
        return out
    def evaluate(self,inputs):
        v=list(inputs)
        for op,a,b in self.gates: v.append((v[a]&v[b]) if op=='&' else (v[a]|v[b]))
        return v
def plane(q):
    reps=[p for p in product(range(q),repeat=3) if any(p) and next(x for x in p if x)==1]
    return [[j for j,l in enumerate(reps) if sum(a*b for a,b in zip(p,l))%q==0] for p in reps]
def fixture(stars,mode,seed):
    n=len(stars)
    c=Circuit(2*n)
    def add(a,b):return c.gate('|',a,b)
    def mul(a,b):return c.gate('&',a,b)
    def either(xs):return c.reduce('|',xs)
    if mode=='mixed':
        x=seed%n
        z=next(l for l in range(n) if l not in stars[x])
        row=either([n+j for j in stars[x]])
        col=either([i for i in range(n) if z in stars[i]])
        g=add(mul(x,row),mul(n+z,col))
        other=[mul(i,n+l) for i in range(n) for l in stars[i] if i!=x and l!=z]
        return c,either([add(g,mul(g,row))]+other)
    rows=[mul(i,either([n+j for j in stars[i]])) for i in range(n)]
    if mode=='root':return c,either(rows)
    rng=Random(seed)
    rng.shuffle(rows)
    chunks=[]
    for k in range(0,n,3):
        g=either(rows[k:k+3])
        chunks.append(add(g,mul(g,n+rng.randrange(n))))
    return c,either(chunks)
def extract(c,out,neighbors,query):
    total=c.n+len(c.gates)
    uses=[[] for _ in range(total)]
    for i,(_,a,b) in enumerate(c.gates,c.n):
        uses[a].append(i)
        uses[b].append(i)
    comp=[None]*total
    for i in reversed(range(total)):
        assert uses[i] or i==out
        comp[i]=i if len(uses[i])!=1 else comp[uses[i][0]]
    parts={}
    for i,r in enumerate(comp):parts.setdefault(r,[]).append(i)
    n=c.n//2
    data=set(range(c.n))-query
    dst=Circuit(n+2)
    zero,one=n,n+1
    ds={v:j for j,v in enumerate(sorted(data))}
    base=[ds.get(v,zero) for v in range(c.n)]
    for op,a,b in c.gates:
        if zero in (base[a],base[b]):
            base.append(zero if op=='&' else (base[a] if base[b]==zero else base[b]))
        else: base.append(dst.gate(op,base[a],base[b]))
    outputs,kinds={},{}
    for root,nodes in parts.items():
        qs=[v for v in nodes if v in query]
        ld=data.intersection(nodes)
        if not qs:continue
        inside=any(neighbors[x]&ld for x in qs)
        if root==out or inside:kind='output' if root==out else 'internal'
        elif len(qs)>1:kind='anchor'
        elif ld:kind='zeroed'
        else:continue
        if kind=='zeroed':
            x=qs[0]
            def at_zero(v):
                if comp[v]!=root:return base[v]
                if v<c.n:return zero
                op,a,b=c.gates[v-c.n]
                return dst.gate(op,at_zero(a),at_zero(b))
            fs=[]
            while x!=root:
                g=uses[x][0]
                op,a,b=c.gates[g-c.n]
                if op=='&':fs.append(at_zero(b if a==x else a))
                x=g
            outputs[qs[0]]=dst.reduce('&',fs) if fs else one
            kinds[qs[0]]=kind
        else:
            desired=set(qs)
            for v in nodes:
                if v<c.n:continue
                _,a,b=c.gates[v-c.n]
                if a in desired or b in desired:desired.add(v)
            ctx={root:one}
            for v in reversed(nodes):
                if v<c.n or v not in desired:continue
                op,a,b=c.gates[v-c.n]
                for child,other in [(a,b),(b,a)]:
                    if child in desired:
                        ctx[child]=ctx[v] if op=='|' else dst.gate('&',ctx[v],base[other])
            for x in qs:outputs[x],kinds[x]=ctx[x],kind
    assert len(dst.gates)<=min(3*len(c.gates),2*len(c.gates)+len(outputs))
    return dst,outputs,kinds
def run():
    modes=Counter()
    for q in (2,3):
        stars=plane(q)
        n=len(stars)
        adj={i:{n+j for j in stars[i]} for i in range(n)}
        adj.update({n+j:{i for i in range(n) if j in stars[i]} for j in range(n)})
        bits=[sum(1<<m for m in range(1<<n) if m>>j&1) for j in range(n)]
        allbits=(1<<(1<<n))-1
        for name in ['root','mixed','chunks']:
            for seed in range(4):
                src,out=fixture(stars,name,seed)
                combined=0
                good=0
                for query in (set(range(n)),set(range(n,2*n))):
                    dst,outs,kinds=extract(src,out,adj,query)
                    combined+=len(dst.gates)
                    good+=len(outs)
                    vals=dst.evaluate(bits+[0,allbits])
                    data=sorted(set(range(2*n))-query)
                    for x,node in outs.items():
                        modes[kinds[x]]+=1
                        star=sum(1<<j for j,d in enumerate(data) if d in adj[x])
                        radius=q-1 if kinds[x]=='anchor' else q
                        for m in range(1<<n):
                            if m.bit_count()<=radius:
                                assert (vals[node]>>m)&1==int(bool(m&star)),(q,name,kinds[x],x,m)
                assert combined<=4*len(src.gates)+good-n
    assert {'output','zeroed','anchor'}<=modes.keys()
    for q in range(3,397):
        n=q*q+q+1
        numer=(4*n-1)*(q-2)+n-4
        assert 100*((numer+q+1)//(q+2))>=n*q
    print('Verified compiled rows by case:',dict(modes))
    print('Verified integer bounds for every order 3 through 396.')
if __name__=='__main__':run()
