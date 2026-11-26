"""Exact six-input gate search on singleton and unordered pair tests."""
import argparse
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from time import monotonic
import resource
cells=tuple((i,j) for i in range(6) for j in range(i,6))
U=(1<<len(cells))-1
raw=tuple(sorted(sum(1<<t for t,(i,j) in enumerate(cells) if k==i or k==j) for k in range(6)))
T=sum(1<<t for t,(i,j) in enumerate(cells) if 270585021>>(6*i+j)&1)
class Check:
    def __init__(self,target):
        self.t=target
        pairs=[(i,j) for i in range(21) for j in range(21) if target>>i&1 and not target>>j&1]
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

def controls():
    results=[]
    for neighbor in (False,True):
        val=0
        for t,(i,j) in enumerate(cells):
            a,b,x,y,d,e=[k in (i,j) for k in range(6)]
            c=x or y
            output=not ((b and (c if neighbor else (a or c))) or (c and d) or (e and not (a or b)))
            val|=int(output)<<t
        results.append(val)
    assert results==[T,T^2] and T==302717
    for k in range(6):
        assert any(i!=k and ((270585021>>(6*i+i))^(270585021>>(6*min(i,k)+max(i,k))))&1 for i in range(6))
    assert Check(raw[0]|raw[1]).decide(raw[:2],1,0)
    assert Check(U^(raw[0]&raw[1])).decide(raw[:2],1,1)
    print('controls: all 21 cells, upper10 and adjacent9; every raw essential; two small register positives',flush=True)
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--positive',action='store_true')
    args=parser.parse_args();controls()
    requests=[(T^2,7,2),(T,8,2)] if args.positive else [(T,b,9-b) for b in [5,6,7,8,9]]
    for target,b,n in requests:
        c=Check(target)
        clock=monotonic()
        decision=c.decide(raw,b,n)
        print(target,b,n,int(decision),round(monotonic()-clock,3),resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
        assert decision==args.positive
