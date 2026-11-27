"""Verify one four-prefix receipt against the frozen graph, using only stdlib."""
import hashlib
import json
from pathlib import Path
import re
import sys

def require(test, message):
    if not test:raise ValueError(message)

def verify(receipt,control):
    p=json.loads(receipt.read_text())
    src=control.read_bytes()
    require(hashlib.sha256(src).hexdigest()=='08b07ebb1edfb826bb061afcc09558ae5d75a6d4d626e43c373c4d8e6855d731','control')
    rows=[int(x,16) for x in re.findall(rb'0x([0-9a-fA-F]+)',src)]
    codes=[tuple(map(int,g)) for g in re.findall(rb'\((\d+),(\d+),(\d+)\)',src)]
    require(len(codes)==180 and len(rows)==32,'control structure')
    features=p['features']
    keep=[24,63,74,86,88,99,106,109,112,131,134,136,141,154,208]
    options=[[[79,81],[31,49]],[[50,81],[49,110]]]
    require(any(features==keep+[153,121,[23,68],[60,212]]+o+[85] for o in options),'feature map')
    paid=sorted({s for f in features for s in ([f] if isinstance(f,int) else f)}|{244,1000000})
    require(p['bank']==paid,'physical donor order')
    prefix=[];projection=[]
    for f in features:
        if isinstance(f,int):projection.append(paid.index(f))
        else:
            projection.append(len(paid)+len(prefix))
            prefix.append([1,paid.index(f[0]),paid.index(f[1])])
    require(prefix==p['prefix'] and projection==p['projection'],'prefix mapping')
    ports=[220,223,224,225,226]
    # Collapse zero taps with a distinct formal variable assigned to the scalar tap.
    cache=dict(zip(ports,[-2,-1,-1,-1,-1])); needed=set()
    def simplify(w):
        if w<64:return w
        if w in cache:return cache[w]
        o,a,b=codes[w-64];a,b=simplify(a),simplify(b)
        if a==b:out=a
        elif -1 in (a,b):out=(b if a==-1 else a) if o==1 else -1
        else:out=w;needed.add(w)
        cache[w]=out
        return out
    for w in [243,121]+[s for s in paid if s<244]:simplify(w)
    require(len(needed)==136 and p['fixed_with_prefix']==141 and p['tail_cap']==29,'physical cost')
    new={};old={};common={};cells=[];links=set();marker=0;fixed_count=0
    for r in range(32):
        for c in range(32):
            v=[int(i in (r,32+c)) for i in range(64)]
            for o,a,b in codes:v.append(v[a]&v[b] if o==0 else v[a]|v[b])
            y=rows[r]>>c&1
            require(v[243]==y,'full output')
            if r==c and r<6:marker|=(1-v[121])<<r
            if any(v[i] for i in range(213,229) if i not in ports):
                fixed_count+=1
                continue
            def key(bits):return sum(x<<j for j,x in enumerate(bits))
            x=key(v[f] if isinstance(f,int) else v[f[0]]|v[f[1]] for f in features)
            z=key([v[f] for f in keep]+[v[153]&(1-v[121]),v[85]|v[121],v[23]|v[68],v[60]|v[212],v[50]|v[81],v[31]|v[49]])
            shared=key([v[f] for f in keep]+[v[23]|v[68],v[60]|v[212],v[features[20][0]]|v[features[20][1]] if features[20]==[31,49] else v[50]|v[81]])
            common.setdefault(shared,set()).add(y)
            require(new.setdefault(x,y)==y and old.setdefault(z,y)==y,'care conflict')
            links.add((z,x));cells.append([32*r+c,x,y])
    layout=0 if features[19]==[79,81] else 1
    require(marker==53 and fixed_count==313 and len(cells)==711 and sum(y for _,_,y in cells)==98,'raw counts or marker')
    require(cells==p['rows'] and sorted(new.items())==list(map(tuple,p['care'])),'physical labels')
    require((len(new),sum(new.values()))==((498,88) if layout==0 else (496,88)),'new counts')
    require((p['raw_cells'],p['distinct_vectors'],p['positive_patterns'])==(711,len(new),88),'receipt totals')
    require(len(old)==469 and sum(old.values())==84,'historical counts')
    signs=[]
    for j in range(22):
        v={t for x,t in new.items() if not x&(1<<j) and new.get(x|(1<<j))==1-t}
        require(v,'inessential coordinate')
        signs.append(len(v))
    old_degrees={z:0 for z in old};new_degrees={x:0 for x in new}
    for z,x in links:old_degrees[z]+=1;new_degrees[x]+=1
    one_to_one=sum(old_degrees[z]==new_degrees[x]==1 for z,x in links)
    return dict(marker=marker,care_cells=len(cells),positive_cells=98,negative_cells=613,essential=len(signs),
                binate=sum(n==2 for n in signs),unate_slots=[j for j,v in enumerate(signs) if v==1],
                old_signatures=len(old),new_signatures=len(new),positive_signatures=sum(new.values()),
                shared_signal_count=18,shared_signal_signatures=len(common),mixed_labels_on_shared_signals=sum(len(t)>1 for t in common.values()),
                identical_cell_fibers=one_to_one,old_fibers_changed=len(old)-one_to_one,new_fibers_changed=len(new)-one_to_one,
                old_fibers_split=sum(n>1 for n in old_degrees.values()),new_fibers_merging_old=sum(n>1 for n in new_degrees.values()))
if __name__=='__main__':
    here=Path(__file__).resolve().parent
    print(json.dumps(verify(Path(sys.argv[1]),Path(sys.argv[2]) if len(sys.argv)>2 else here/'package/projected21-tail-20579/control.lean'),sort_keys=True))
