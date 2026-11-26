from itertools import product
from partial_atom import feasible

class Envelope:
    def __init__(self,n,samples):
        self.n=n;self.samples=dict(samples);self.pivots={}
        present=[v for v,p in samples.items() if p>=0]
        self.origin=present[0] if present else None
        if present:
            for v in present:
                r=self.rem(v^self.origin)
                if r:self.pivots[r.bit_length()-1]=r
        self.forbidden={self.rem(v) for v,p in samples.items() if p<0}
    def rem(self,v):
        for j in sorted(self.pivots,reverse=True):
            if v>>j&1:v^=self.pivots[j]
        return v
    def domain(self,x):
        if x in self.samples:return {self.samples[x]}
        if self.rem(x) in self.forbidden:return {-1}
        if self.origin is None or self.rem(x)!=self.rem(self.origin):return {-1,0,1,2,3}
        return {v for v in range(4) if feasible(self.n,self.samples|{x:v})}
if __name__=='__main__':
    for row in product([None,-1,0,1,2,3],repeat=4):
        obs={i:v for i,v in enumerate(row) if v is not None}
        if not feasible(2,obs):continue
        env=Envelope(2,obs)
        for x in range(4):
            if x not in obs:
                assert env.domain(x)=={v for v in range(-1,4) if feasible(2,obs|{x:v})}
    print('all feasible partial two-bit query domains passed')
