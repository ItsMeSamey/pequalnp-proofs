from pathlib import Path
from itertools import combinations
import json,hashlib,re
here=Path(__file__).resolve().parent
meta=json.loads((here/'last14-support-certificate.json').read_text())
raw=Path(meta['source']).read_bytes();assert hashlib.sha256(raw).hexdigest()==meta['sha256']
net=json.loads(raw)['net']
rows=[int(x,16) for x in re.findall(r'0x[0-9a-fA-F]+', json.load(open('/tmp/pnp-official-20579-public.json'))['gap']['statement'])]
cells=[]
for i in range(1024):
    r,c=divmod(i,32);v=[j in (r,32+c) for j in range(64)]
    for g in net['gates']:
        a=[v[k] for k in g['inputs']];op=g['op']
        v.append(all(a) if op=='and' else any(a) if op=='or' else not a[0])
    cells.append((v,rows[r]>>c&1))
assert sum(v[net['output']]!=y for v,y in cells)==14
def check(wires,control):
    T={};cell={}
    for i,(v,y) in enumerate(cells):
        key=sum(v[w]<<k for k,w in enumerate(wires));z=int(v[net['output']]) if control else y
        assert T.setdefault(key,z)==z;cell.setdefault(key,i)
    keys=sorted(T,key=int.bit_count)
    downs=0;dp={};alt={};starts0={}
    for j,x in enumerate(keys):
        subs=[z for z in keys[:j] if z&x==z]
        downs+=sum(T[z]>T[x] for z in subs)
        best=max(((dp[z][0]+(T[z]>T[x]),z) for z in subs),default=(0,None))
        dp[x]=best
        alt[x]=max(((alt[z][0]+1,z) for z in subs if T[z]!=T[x]),default=(1,None))
        starts0[x]=max(((starts0[z][0]+1,z) for z in subs if T[z]!=T[x] and starts0[z][0]),default=(1 if T[x]==0 else 0,None))
    def chain(tab):
        x=max(keys,key=lambda x:tab[x][0]);n=tab[x][0];out=[]
        while x is not None:out.append([cell[x],T[x],x]);x=tab[x][1]
        return n,out[::-1]
    d,wd=chain(dp);a,wa=chain(alt);b,wb=chain(starts0)
    piv={}
    for j,w in enumerate(wires):
        h={}
        for x,y in T.items():
            nxt=x|(1<<j)
            if x!=nxt and T.get(nxt)==1-y:h.setdefault('fall' if y else 'rise',[cell[x],cell[nxt]])
        if len(h)==2:piv[w]=h
    return dict(patterns=len(T),descents=downs,max_drops=d,minimum_NOT=d.bit_length(),drop_chain=wd,
                longest_alternating=a,alt_chain=wa,longest_starting_zero=b,zero_chain=wb,binate=piv)
out={}
for k in range(3):
    for choice in combinations(meta['optional'],k):
        w=[v for v in meta['bank'] if v not in meta['optional'] or v in choice]
        rec={nm:check(w,c) for nm,c in [('target',False),('control',True)]}
        out[str(choice)]=rec
        r=rec['target'];up=next(a['upstream'] for a in meta['valid'] if a['extra']==list(choice))
        print(choice,r['patterns'],r['descents'],r['max_drops'],r['longest_starting_zero'],len(r['binate']),up+len(w)-1+bool(r['binate'])+r['minimum_NOT'],r['drop_chain'])
(here/'enriched30-chains.json').write_text(json.dumps(out,indent=2))
