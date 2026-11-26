"""Portable live-register search on the sixteen normalized cells."""
import argparse,json
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from time import monotonic
U=65535
SUP=tuple(15<<(4*i) for i in range(4))+tuple(4369<<i for i in range(4))
T=43333
class Check:
    def __init__(self,target):
        self.t=target
        pairs=[(i,j) for i in range(16) for j in range(16) if target>>i&1 and not target>>j&1]
        self.all=(1<<len(pairs))-1
        @lru_cache(None)
        def positive(a):
            return sum(1<<k for k,(i,j) in enumerate(pairs) if a>>i&1 and not a>>j&1)
        self.positive=positive
        @lru_cache(maxsize=28000)
        def extend(F,b,n):
            r=b+1-len(F)
            for unary in (False,True):
                if unary and not n or not unary and not b:continue
                for used in combinations(F,1 if unary else 2):
                    vals=(U^used[0],) if unary else (used[0]&used[1],used[0]|used[1])
                    for z in vals:
                        if z==target:return True
                        if z in (0,U) or z in F:continue
                        base=set(F)-set(used)
                        for cost in range(min(len(used),r)+1):
                            for keep in combinations(used,cost):
                                F1=tuple(sorted(base|set(keep)|{z}))
                                if self.decide(F1,b-int(not unary),n-int(unary)):return True
            return False
        self.extend=extend
    def decide(self,F,b,n):
        if self.t in F:return True
        if len(F)>b+1:return False
        if b==0:return bool(n and len(F)==1 and F[0]^U==self.t)
        cover=0
        for a in F:
            cover|=self.positive(a)
            if n:cover|=self.positive(U^a)
        if cover!=self.all:return False
        return self.extend(F,b,n)
def keys():
    for k in range(256):
        if min((k&15).bit_count(),(k>>4).bit_count())<3:continue
        d=k.bit_count();p=(k&136).bit_count()
        for b in range(d-1,10-p):yield k,b,9-p-b
def control():
    ops=json.loads((Path(__file__).resolve().parents[1]/'baseline10.json').read_text())
    raw=[sum(1<<(5*r+c) for r in range(5) for c in range(5) if r==i) for i in range(5)]
    raw +=[sum(1<<(5*r+c) for r in range(5) for c in range(5) if c==i) for i in range(5)]
    for op,*idx in ops:
        a=raw[idx[0]]
        raw.append(((1<<25)-1)^a if op=='not' else a&raw[idx[1]] if op=='and' else a|raw[idx[1]])
    assert raw[-1]==7879121 and len(ops)==10
    assert sum(((raw[-1]>>(5*r+c))&1)<<(4*i+j) for i,r in enumerate((0,3,4,1)) for j,c in enumerate((0,3,4,1)))==T
    for t,b,n in [(SUP[0]|SUP[4],1,0),((SUP[0]&SUP[4])^U,1,1)]:
        assert Check(t).decide(tuple(sorted((SUP[0],SUP[4]))),b,n)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('log');p.add_argument('--keys',type=int,nargs='*');args=p.parse_args()
    control();out=Path(args.log)
    done={tuple(map(int,s.split()[:3])) for s in out.read_text().splitlines()} if out.exists() else set()
    c=Check(T)
    order=sorted(keys(),key=lambda z:(int(z[2]!=0),z[1]+1-z[0].bit_count(),z[2],z[0]))
    print('CONTROLS PASS; keys:',len(order),flush=True)
    for k,b,n in order:
        if args.keys is not None and k not in args.keys:continue
        if (k,b,n) in done:continue
        t=monotonic()
        F=tuple(sorted(x for i,x in enumerate(SUP) if k>>i&1))
        res=c.decide(F,b,n)
        with out.open('a') as f:print(k,b,n,int(res),round(monotonic()-t,3),file=f,flush=True)
        if res:print('POSITIVE',k,b,n,flush=True);break
