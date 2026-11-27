from itertools import product

def sat2(n,clauses):
    """Literals are pairs (variable, value that makes the literal true)."""
    g=[[] for _ in range(2*n)]; rev=[[] for _ in g]
    for c in clauses:
        if not c: return None
        if len(c)>2: raise ValueError('nonbinary residual')
        a=2*c[0][0]+c[0][1]; b=2*c[-1][0]+c[-1][1]
        for s,t in ((a^1,b),(b^1,a)):
            g[s].append(t); rev[t].append(s)
    order=[]; seen=set()
    for root in range(2*n):
        stack=[(root,False)]
        while stack:
            v,end=stack.pop()
            if end: order.append(v); continue
            if v in seen: continue
            seen.add(v); stack.append((v,True))
            stack.extend((u,False) for u in g[v] if u not in seen)
    comp=[-1]*(2*n)
    for i,v in enumerate(reversed(order)):
        if comp[v]>=0: continue
        stack=[v]; comp[v]=i
        while stack:
            for u in rev[stack.pop()]:
                if comp[u]<0: comp[u]=i; stack.append(u)
    if any(comp[2*v]==comp[2*v+1] for v in range(n)): return None
    return sum((comp[2*v+1]>comp[2*v])<<v for v in range(n))

class Chart:
    def __init__(self,n,formula):
        self.n=n; self.blocks=[]; self.vars=[]; self.edge_cols=[]
        occurrences=[[] for _ in range(n)]; offset=0
        for clause in formula:
            literals=sorted(set(clause))
            if any((v,1-s) in literals for v,s in literals): continue
            if not literals: raise ValueError('empty clause is an immediate SAT rejection')
            j=len(self.vars); start=len(self.edge_cols)
            for v,s in literals:
                i=len(self.vars); self.vars.append(v); occurrences[v].append(i)
                offset |= (1^s)<<i
            for k in range(1,len(literals)): self.edge_cols.append((1<<j,1<<(j+k)))
            self.blocks.append((j,len(literals),start))
        self.checks=[(inds[0],i) for inds in occurrences for i in inds[1:]]
        self.target=self.syndrome(offset)
        self.offset=offset
        self.labels=[(self.syndrome(a),self.syndrome(b)) for a,b in self.edge_cols]

    def syndrome(self,z):
        return sum((((z>>a)^(z>>b))&1)<<i for i,(a,b) in enumerate(self.checks))

    def query(self,counts,target,backdoor):
        """Return witness options for the requested sum; retain each physical copy."""
        if len(counts)!=len(self.labels) or any(c<0 for c in counts): raise ValueError('bad counts')
        if target<0 or target.bit_length()>len(self.checks): return None
        y=sum(((target>>i)&1)<<b for i,(_,b) in enumerate(self.checks))
        clauses=[]
        for j,k,s in self.blocks:
            req=lambda i:(self.vars[i],(y>>i)&1)
            present=[a for a in range(1,k) if counts[s+a-1]]
            clauses.extend(((req(j+a),)) for a in range(1,k) if not counts[s+a-1])
            if not any(counts[s+a-1]>=2 for a in present):
                clauses.append(tuple(req(j+a) for a in [0]+present))
        for bits in product((0,1),repeat=len(backdoor)):
            fix=dict(zip(backdoor,bits)); residual=[]
            for c in clauses:
                if not any(fix.get(v)==b for v,b in c):
                    residual.append([(v,b) for v,b in c if v not in fix])
            if any(len(c)>2 for c in residual): raise ValueError('insufficient supplied backdoor')
            x=sat2(self.n,residual+[[p] for p in fix.items()])
            if x is None: continue
            z=y^sum(((x>>v)&1)<<i for i,v in enumerate(self.vars))
            paths=[[0]*c for c in counts]
            for j,k,s in self.blocks:
                need=(z>>j)&1
                for a in range(1,k):
                    e=s+a-1; private=(z>>(j+a))&1
                    if private: paths[e][0]=2
                    if need and counts[e]>private:
                        paths[e][private]=1; need=0
                assert not need
            val=0
            for steps,(a,b) in zip(paths,self.labels):
                for choice in steps: val ^= (0,a,b)[choice]
            assert val==target
            return x,paths
        return None

    def decode_full(self,paths):
        """Recover the original variables from one physical choice per original edge."""
        if len(paths)!=len(self.edge_cols) or any(len(p)!=1 for p in paths):
            raise ValueError('expected one original choice per edge')
        z=self.offset
        for (a,b),p in zip(self.edge_cols,paths):
            z ^= (0,a,b)[p[0]]
        assignment={}
        for i,v in enumerate(self.vars):
            b=z>>i&1
            if assignment.setdefault(v,b)!=b:
                raise ValueError('inconsistent occurrence copies')
        return sum(value<<v for v,value in assignment.items())

    def intersect(self,left,right,delta,backdoor):
        if len(left)!=len(self.labels) or len(right)!=len(self.labels): raise ValueError('bad profile')
        both=self.query([a+b for a,b in zip(left,right)],delta,backdoor)
        if both is None: return None
        _,paths=both
        return ([p[:i] for p,i in zip(paths,left)], [p[i:] for p,i in zip(paths,left)])
