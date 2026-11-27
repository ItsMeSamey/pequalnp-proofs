"""Bind both marker receipts to every physical care cell and to the prepaid NOT."""
from pathlib import Path
import json
import re
from verify_four_geometry import require, verify

def replay(positive, marker, control):
    metrics = verify(positive,control)
    p = json.loads(positive.read_text())
    m = json.loads(marker.read_text())
    require(m['bank']==p['bank'] and m['bank'].count(244)==1,'prepaid donor')
    require(m['features']==p['features']+[244] and p['features'][16]==121,'selector slots')
    require(m['projection']==p['projection']+[p['bank'].index(244)] and m['prefix']==p['prefix'],'tail mapping')
    require(m['fixed_with_prefix']==p['fixed_with_prefix']==141 and m['tail_cap']==29,'charge')
    codes=[tuple(map(int,g)) for g in re.findall(rb'\((\d+),(\d+),(\d+)\)',control.read_bytes())]
    emitted=[]; rem={i:i for i in range(64)}
    def old(w):
        if w not in rem:
            op,a,b=codes[w-64]; a,b=old(a),old(b)
            rem[w]=64+len(emitted); emitted.append((op,a,b))
        return rem[w]
    anchor=old(121)
    marker_wire=64+len(emitted); emitted.append((2,anchor,anchor))
    require(marker_wire==70 and anchor==69 and all(o in (0,1) for o,a,b in emitted[:-1]),'first internal NOT')
    all_marker={}
    for cell in range(1024):
        r,c=divmod(cell,32)
        v=[int(i in (r,32+c)) for i in range(64)]
        for o,a,b in emitted:
            v.append(v[a]&v[b] if o==0 else v[a]|v[b] if o==1 else 1-v[a])
        all_marker[cell]=v[marker_wire]
    require(sum(all_marker[33*j]<<j for j in range(6))==53,'marker diagonal')
    rows=[]
    for cell,x,y in p['rows']:
        bit=all_marker[cell]
        require(bit==1-((x>>16)&1),'physical complement')
        rows.append([cell,x|(bit<<22),y])
    require(rows==m['rows'] and sorted({(x,y) for _,x,y in rows})==list(map(tuple,m['care'])),'marker care')
    require((m['raw_cells'],m['distinct_vectors'],m['positive_patterns'])==(711,metrics['new_signatures'],88),'marker totals')
    return metrics
