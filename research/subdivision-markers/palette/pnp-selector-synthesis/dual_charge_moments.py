"""Factored moment recovery on indexed plane-dual edges."""
from collections import deque


class ChargeMoments:
    def __init__(self,n,edges):
        self.edges=list(edges)
        self.graph=[[] for _ in range(n)]
        self.charge=[0]*n
        for i,(u,v,b) in enumerate(self.edges):
            if not (0<=u<n and 0<=v<n and 0<=b<4):
                raise ValueError("invalid dual edge")
            self.charge[u]^=b
            self.charge[v]^=b
            self.graph[u].append((v,i))
            self.graph[v].append((u,i))
        self.terminals=[i for i,b in enumerate(self.charge) if b]
        self.bits=[sum(((self.charge[v]>>j)&1)<<i for i,v in enumerate(self.terminals)) for j in (0,1)]

    def read(self,support):
        """Integrate an original edge mask; a noncut has no such face labels."""
        if support<0 or support.bit_length()>len(self.edges):
            raise ValueError("invalid support")
        if not self.graph:
            return 0
        root=self.terminals[-1] if self.terminals else 0
        labels={root:0}
        queue=deque([root])
        while queue:
            u=queue.popleft()
            for v,i in self.graph[u]:
                val=labels[u]^((support>>i)&1)
                if v in labels:
                    if labels[v]!=val:
                        raise ValueError("not a dual cut")
                else:
                    labels[v]=val
                    queue.append(v)
        if len(labels)!=len(self.graph):
            raise ValueError("disconnected dual")
        return sum(labels[v]<<i for i,v in enumerate(self.terminals))

    def pair(self,left,right):
        a,b=self.read(left),self.read(right)
        if any((c&v).bit_count()%2 for c in self.bits for v in (a,b)):
            raise ValueError("terminal readings not zero charge")
        return tuple((a&b&c).bit_count()%2 for c in self.bits)

    def projected(self):
        """Matrices on the formal terminal quotient; equality for W-perp requires certificate."""
        pivots={}
        X=[]
        for k,v in enumerate(self.terminals[:-1]):
            x=self.charge[v]
            mask=1<<k
            while x:
                p=x.bit_length()-1
                if p not in pivots:
                    pivots[p]=x,mask
                    break
                row,z=pivots[p]
                x^=row
                mask^=z
            else:
                X.append(mask)
        return tuple(X),tuple(tuple(sum(((a&b&c).bit_count()%2)<<j for j,b in enumerate(X))
                                    for a in X) for c in self.bits)
