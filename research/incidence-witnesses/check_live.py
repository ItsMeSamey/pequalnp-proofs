from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'anchored'))
from check import Circuit,plane,fixture

def engineered(stars,shared):
    n=len(stars); c=Circuit(2*n)
    l=stars[0][0]
    def truth():return c.gate('&',0,n+l)
    common=truth() if shared else None
    proxies=[0]+[c.gate('|',i,common if shared else truth()) for i in range(1,n)]
    parts=[c.gate('&',proxies[i],n+j) for i in range(n) for j in stars[i] if (i,j)!=(0,l)]
    return c,c.reduce('|',parts)

def compile_detectors(c,out):
    total=c.n+len(c.gates)
    uses=[[] for _ in range(total)]
    for i,(_,a,b) in enumerate(c.gates,c.n):
        uses[a].append(i); uses[b].append(i)
    owner=[None]*total
    for i in reversed(range(total)):
        assert uses[i] or i==out
        owner[i]=i if len(uses[i])!=1 else owner[uses[i][0]]
    groups={}
    for i,r in enumerate(owner):groups.setdefault(r,[]).append(i)
    singleton=c.evaluate([1<<i for i in range(c.n)])
    live={}
    for r,nodes in groups.items():
        local=[v for v in nodes if v<c.n]
        if r!=out and len(local)==1 and singleton[r]&(1<<local[0]):live[r]=local[0]
    path={}
    for r in sorted(groups,reverse=True):
        local=any(v<c.n for v in groups[r])
        path[r]=1 if r==out or local else sum(path[owner[u]] for u in uses[r])
    raw=sum(len(uses[r]) for r in live)
    limit=max(path.values())
    dst=Circuit(c.n+1); zero=c.n
    repl={}; outputs=[]; lengths={}; leaves=0
    for r in sorted(groups):
        nodes=groups[r];loc={};ln={}
        def get(v):return loc[v] if owner[v]==r else repl[owner[v]]
        def length(v):return ln[v] if owner[v]==r else lengths[owner[v]]
        for v in nodes:
            if v<c.n:loc[v],ln[v]=zero,0
            else:
                op,a,b=c.gates[v-c.n];i,j=get(a),get(b)
                if zero in (i,j):
                    loc[v]=zero if op=='&' else (j if i==zero else i)
                    ln[v]=0 if op=='&' else length(a)+length(b)
                else:
                    loc[v]=dst.gate(op,i,j)
                    ln[v]=length(a)+length(b)
        if r==out or any(v<c.n for v in nodes):
            if loc[r]!=zero:outputs.append(loc[r]);leaves+=ln[r]
            repl[r]=live.get(r,zero); lengths[r]=int(r in live)
        else:repl[r],lengths[r]=loc[r],ln[r]
    dout=dst.reduce('|',outputs) if outputs else zero
    assert leaves<=limit*raw
    return dst,dout,set(live.values()),limit,raw,leaves

def run():
    cases=0; active=False; large=False
    for q in (2,3):
        stars=plane(q);n=len(stars)
        samples=[fixture(stars,mode,i) for mode in ('root','mixed','chunks') for i in range(2)]
        samples.extend(engineered(stars,flag) for flag in (False,True))
        for c,out in samples:
            d,r,live,m,f,leaves=compile_detectors(c,out)
            es=[(p,n+j) for p in range(n) for j in stars[p] if p in live and n+j in live]
            tests=[(1<<p|1<<j,1) for p,j in es]
            pts=sorted(i for i in live if i<n)
            lns=sorted(i for i in live if i>=n)
            for k in range(q):
                for pp in combinations(pts,k):
                    available=[j for j in lns if all(j-n not in stars[p] for p in pp)]
                    for h in range(q):
                        for ll in combinations(available,h):tests.append((sum(1<<v for v in (*pp,*ll)),0))
            packed=[sum(1<<k for k,(mask,_) in enumerate(tests) if mask>>i&1)
                    for i in range(2*n)]
            expected=sum(answer<<k for k,(_,answer) in enumerate(tests))
            assert d.evaluate(packed+[0])[r]==expected
            assert c.evaluate(packed)[out]==expected
            h=2*n-len(live)
            assert (q+1)*h<=m*f
            assert n*q<=2*m*(len(c.gates)+1-h)
            active|=(len(live)==2*n and m==1 and leaves>0)
            large|=(m>1)
            cases+=1
    assert active and large
    print('Verified positive flags, all live sparse negatives, leaf and path bounds on',cases,'circuits.')
if __name__=='__main__':run()
