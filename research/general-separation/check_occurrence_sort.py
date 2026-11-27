"""Small binary-key native bitonic rows. Literal bit 1 means negated."""
from itertools import product
from occurrence_correction import correct_violations


class Net:
    def __init__(self,cs):
        self.n=n=4*len(cs)
        self.h=n.bit_length()-1
        self.next=[2]*n
        self.rec={}
        self.pins={}
        def gate(r,t,a,b):
            w=128*r+self.next[r]
            self.next[r]+=1
            assert self.next[r]<=128
            self.rec[w]=t,a,b
            return w
        self.keys=[c[min(j,2)][0] for c in cs for j in range(4)]
        lanes=[(128*r,128*r+1) for r in range(n)]
        self.pins.update((128*r,b) for r,b in enumerate(self.keys))
        for k in range(1,self.h+1):
            for j in reversed(range(k)):
                new=[]
                for r in range(n):
                    l=r & ~(1<<j)
                    hi=l | (1<<j)
                    (a,u),(b,v)=lanes[l],lanes[hi]
                    flip=gate(r,2 if r>>k&1 else 4,a,b)
                    def mux(x,y):
                        if r==hi:
                            x,y=y,x
                        return gate(r,14,gate(r,2,flip,x),gate(r,8,flip,y))
                    new.append((mux(a,b),mux(u,v)))
                lanes=new
        for r in range(n-1):
            a,u=lanes[r]
            b,v=lanes[r+1]
            self.pins[gate(r,14,gate(r,6,a,b),gate(r,9,u,v))]=1
        for i,c in enumerate(cs):
            r=4*i
            lits=[]
            for j,(_,neg) in enumerate(c):
                w=(r+j)*128+1
                lits.append(gate(r,7,w,w) if neg else w)
            self.pins[gate(r,14,gate(r,14,*lits[:2]),lits[2])]=1

    def decode(self,j):
        w,s=divmod(j,8)
        if w in self.rec and s<4:
            t,a,b=self.rec[w]
            return ((a,s>>1),(b,s&1),(w,1-(t>>s&1)))
        if w in self.pins and s==4:
            return ((w,1-self.pins[w]),)*3
        return None

    def incident(self,w):
        r=w//128
        rows={r,r-1,r+1}|{r^(1<<j) for j in range(self.h)}|{(r&~3)+p for p in range(4)}
        for v in rows:
            if 0<=v<self.n:
                for u in range(self.next[v]):
                    for s in range(5):
                        j=(128*v+u)*8+s
                        if any(a==w for a,_ in self.decode(j) or ()):
                            yield j

    def trace(self,seed):
        bits={128*r:k for r,k in enumerate(self.keys)}
        bits.update({128*r+1:b for r,b in enumerate(seed)})
        for w,(t,a,b) in self.rec.items():
            bits[w]=t>>(2*bits[a]+bits[b])&1
        return bits


def main():
    overlap=repair=False
    for cs in [(((1,0),(0,1),(1,0)),), (((1,0),)*3,((1,1),)*3)]:
        f=Net(cs)
        q=f.h+10
        active={j:c for j in range(1<<q) if (c:=f.decode(j)) is not None}
        reverse={}
        for j,c in active.items():
            for w,_ in c:
                reverse.setdefault(w,set()).add(j)
        selected=list(reverse) if f.n==4 else list(reverse)[::11]
        for w in selected+[127,128*f.n]:
            assert set(f.incident(w))==reverse.get(w,set())
        assert f.decode(7) is None and f.decode(128*f.n*8) is None
        def bad(c,env):
            return int(all(env[w]==neg for w,neg in c))
        projected=set()
        for seed in product((0,1),repeat=f.n):
            env=f.trace(seed)
            if all(env[w]==v for w,v in f.pins.items()):
                assert all(seed[i]==seed[j] for i in range(f.n) for j in range(i)
                           if f.keys[i]==f.keys[j])
                projected.add(tuple(seed[f.keys.index(i)] if i in f.keys else None for i in range(2)))
        expected={tuple(bits[i] if i in f.keys else None for i in range(2))
                  for bits in product(range(2),repeat=2)
                  if all(any(bits[w]!=neg for w,neg in c) for c in cs)}
        assert projected==expected
        old=f.trace([1]*f.n)
        new=dict(old)
        labels=sorted([0,128,next(iter(f.rec))])
        for w in labels:
            new[w]^=1
        hits=[j for w in labels for j in reverse[w]]
        overlap |= len(hits)>len(set(hits))
        for a,b in ((old,new),(new,old)):
            base=sum(bad(c,a) for c in active.values())
            truth=sum(bad(c,b) for c in active.values())
            res=correct_violations(q,q-3,f.decode,f.incident,a.__getitem__,
                                   [(w,b[w]) for w in labels],base,max_emissions_per_label=1000)
            assert res.violations==truth and res.affected_ids==len(set(hits))
            repair |= res.old_affected>res.new_affected
    assert overlap and repair
    print('Bitonic rows, physical gate IDs, projection and signed corrections passed.')


if __name__=='__main__':
    main()
