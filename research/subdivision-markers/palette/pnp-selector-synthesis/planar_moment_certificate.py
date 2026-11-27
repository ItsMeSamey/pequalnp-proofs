"""Check face-label certificates and stream physical-index compatible pairs."""
from itertools import combinations
from dual_charge_moments import ChargeMoments


class CertifiedDual(ChargeMoments):
    def __init__(self,n,edges):
        if n<1:
            raise ValueError("a connected plane dual needs a vertex")
        super().__init__(n,tuple(tuple(e) for e in edges))
        self.read(0)  # Validate connectivity of the supplied dual.

    def cut(self,labels):
        return sum(((((labels>>u)^(labels>>v))&1)<<i) for i,(u,v,_) in enumerate(self.edges))

    def signature(self,labels):
        return frozenset(v for v in self.terminals if labels>>v&1)

    def compatible(self,x,y):
        n=len(self.graph)
        if x<0 or y<0 or (x|y).bit_length()>n:
            return False
        seen=set()
        for seed in range(n):
            if seed in seen:
                continue
            stack=[seed]
            seen.add(seed)
            charge=0
            while stack:
                u=stack.pop()
                charge ^= self.charge[u]
                for v,_ in self.graph[u]:
                    if v not in seen and not ((((x>>u)^(x>>v))|((y>>u)^(y>>v)))&1):
                        seen.add(v);stack.append(v)
            if charge:
                return False
        return True

    def circuits(self):
        for a,b in combinations(self.terminals,2):
            if self.charge[a]==self.charge[b]:
                yield frozenset((a,b))
        for a,b,c in combinations(self.terminals,3):
            if self.charge[a]^self.charge[b]^self.charge[c]==0:
                yield frozenset((a,b,c))

    def check(self,single,pinned,pairs):
        """Returns a generator of genuine physical wedges only after all certificates pass."""
        pinned=dict(pinned)
        pairs={k:tuple(v) for k,v in pairs.items()}
        circuits=list(self.circuits())
        neutrals=[v for v,q in enumerate(self.charge) if not q]
        for v in neutrals:
            if not self.compatible(1<<v,0):
                raise ValueError("neutral singleton")
        for c in circuits:
            x=single[c]
            if self.signature(x)!=c or not self.compatible(x,0):
                raise ValueError("terminal circuit")
        def label_pairs():
            for u,v in combinations(neutrals,2):
                yield 1<<u,1<<v
            for z in neutrals:
                for c in circuits:
                    x=pinned[z,c]
                    if self.signature(x)!=c:
                        raise ValueError("pinned circuit")
                    yield 1<<z,x
            for a,b in combinations(circuits,2):
                if a.isdisjoint(b):
                    x,y=pairs[a,b]
                    if self.signature(x)!=a or self.signature(y)!=b:
                        raise ValueError("terminal pair")
                    yield x,y
        for x,y in label_pairs():
            if not self.compatible(x,y):
                raise ValueError("incompatible face labels")
        return ((self.cut(x),self.cut(y)) for x,y in label_pairs())
