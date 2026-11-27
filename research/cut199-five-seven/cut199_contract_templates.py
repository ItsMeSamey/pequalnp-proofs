import json
from itertools import combinations_with_replacement
from pathlib import Path
root=Path(__file__).resolve().parent
load=lambda n:json.loads((root/n).read_text())
Q=load('cut199-contraction-quartets.json')
supports=load('cut199-contract-supports.json')
allowed={tuple(supports[t['i']]['s']) for t in load('cut199-contract-favorable.json')}
def support(w):return sum((w>>(1<<i)&1)<<i for i in range(5))
ors=[sum(bool(y&m)<<y for y in range(32)) for m in range(32)]
ts={}
for ix,t in enumerate(Q):
    for j,w in enumerate(t['w']):
        fixed={i:support(z) for i,z in enumerate(t['w']) if i!=j};s=support(w)
        for a,b in combinations_with_replacement(range(32),2):
            q=tuple(sorted(list(fixed.values())+[a,b]))
            if q not in allowed:continue
            for op in [0,1]:
                if not (((a|b)==s) if not op else ((a&b)==s and not(ors[a]&ors[b]&~w))):continue
                slots={k:q.index(v)+7 for k,v in fixed.items()}
                slots[j]=[op,q.index(a)+7,q.index(b)+7]
                for g in t['guard']:
                    factors=[]
                    for k,idx in enumerate(t['queries']):
                        center=[0,k,slots[t['bare']]] if idx==g else k
                        factors.append([1,center,slots[idx]])
                    if g<0:factors.append(slots[t['bare']])
                    tree=factors[0]
                    for z in factors[1:]:tree=[0,tree,z]
                    def pairs(t):
                        if isinstance(t,int):return [t],[]
                        l,a=pairs(t[1]);r,b=pairs(t[2])
                        return l+r,a+b+[(min(i,j),max(i,j),t[0]) for i in l for j in r]
                    _,p=pairs(tree)
                    ts[q,tuple(sorted(p))]=(ix,j,a,b,op,g,tree)
out=[dict(s=list(q),pairs=p,source=v[:-1],tree=v[-1]) for (q,p),v in ts.items()]
(root/'cut199-contract-templates.json').write_text(json.dumps(out))
print(len(out))
