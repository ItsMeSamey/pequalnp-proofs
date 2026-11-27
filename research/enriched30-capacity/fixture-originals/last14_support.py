import json,itertools
from pathlib import Path
exec(Path(__file__).with_name('extend_last14.py').read_text().split('edges={')[0])
doc=json.loads(Path(__file__).with_name('last14-extended-bank.json').read_text());B=sorted(bank+doc['extra'])
words=[sum((v>>w&1)<<j for j,w in enumerate(B)) for v,y in keys]
lookup={}
for c,(x,y) in enumerate(keys):lookup[(words[c],y)]=c
essential={}
for j,w in enumerate(B):
    for c,(x,y) in enumerate(keys):
        other=lookup.get((words[c]^(1<<j),1-y))
        if other is not None:essential[w]=[c,other];break
optional=[w for w in B if w not in essential]
def closure(ws):
    seen=set()
    def visit(w):
        if w<64 or w in seen:return
        seen.add(w)
        for t in g[w-64]['inputs']:visit(t)
    for w in [baseline['marker']]+ws:visit(w)
    return sorted(seen)
m=sum(1<<B.index(w) for w in essential);good=[];invalid=[]
for n in range(len(optional)+1):
    for t in itertools.combinations(optional,n):
        selected=sorted([*essential,*t]);mask=m|sum(1<<B.index(w) for w in t)
        labels={}
        for c,key in enumerate(words):
            y=keys[c][1];old=labels.setdefault(key&mask,c)
            if keys[old][1]!=y:invalid.append(dict(extra=t,conflict=[old,c]));break
        else:good.append(dict(extra=t,count=len(selected),upstream=len(closure(selected)),total=len(closure(selected))+len(selected)-1))
print('mandatory',len(essential),'optional',optional,'valid',len(good),'minimum',min(z['total'] for z in good),'donors',min(z['count'] for z in good),flush=True)
res=dict(source=doc['source'],sha256=doc['sha256'],bank=B,mandatory_witness_cells=essential,optional=optional,valid=good,invalid=invalid,minimum_total=min(z['total'] for z in good),minimum_count=min(z['count'] for z in good))
Path(__file__).with_name('last14-support-certificate.json').write_text(json.dumps(res))
