from itertools import combinations
def extend(S,x):
    return S|{a^x for a in S}
def allsp(d):
    out={frozenset({0})}
    for v in range(1,1<<d):
        out|={extend(S,v) for S in out}
    return sorted(out,key=lambda s:(len(s),tuple(sorted(s))))
W=frozenset(range(8))
small=allsp(3)
sid={s:i for i,s in enumerate(small)}
apart=[]
for a,b,c in combinations(range(1,8),3):
    if a^b==c: continue
    p=1|(1<<15)
    for v in a,b,c: p|=1<<sid[frozenset([0,v])]
    for x,y in combinations((a,b,c),2): p|=1<<sid[frozenset((0,x,y,x^y))]
    apart.append(p)
valid=set()
for p in range(1<<16):
    if (p & 32769)!=32769: continue
    union=0
    for a in apart:
        if a&p==a: union|=a
    if union==p: valid.add(p)
def realizers(d):
    allspaces=allsp(d)
    ix={s:i for i,s in enumerate(allspaces)}
    local=[1<<sid[s&W] for s in allspaces]
    adj=[[1<<ix[extend(s,v)] for s in allspaces] for v in range(1<<d)]
    states=[1]*(1<<((1<<d)-1))
    ans={}
    for s in range(1,len(states)):
        lo=s&-s
        v=lo.bit_length()
        old=states[s^lo]
        new=old
        q=old
        while q:
            j=q&-q; q-=j
            new|=adj[v][j.bit_length()-1]
        states[s]=new
        p=0
        while new:
            j=new&-new; new-=j
            p|=local[j.bit_length()-1]
        if p&(1<<15) and (p not in ans or s.bit_count()<ans[p].bit_count()):
            ans[p]=s
    return ans
if __name__=='__main__':
    R=realizers(4)
    print('apartment-closed',len(valid),'material rank≤4 palettes',len(R),'remaining',len(valid-R.keys()),'maximum material size',max(s.bit_count() for s in R.values()))
    import json
    with open('/workspace/scratch/proofsys2026/palette/rank4-witnesses.json','w') as file: json.dump(R,file)
