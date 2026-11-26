"""Check all admissible palettes and construct a single literal configuration per palette."""
import json
from pathlib import Path
from finite import extend, realizers, sid, small, valid, W
def calculate(cols):
    spaces={frozenset([0])}
    for v in cols: spaces|={extend(s,v) for s in spaces}
    return sum(1<<sid[j] for j in {s&W for s in spaces})
def dual_material(cols):
    V=cols+[1,2,4]
    n=len(V)
    rows=[sum(1<<i for i,v in enumerate(V) if v>>b&1) for b in range(max(V).bit_length())]
    used={0}; basis=[]
    for s in range(1<<n):
        if s not in used and all((s&r).bit_count()%2==0 for r in rows):
            basis.append(s)
            used=extend(used,s)
    D=[sum(1<<j for j,row in enumerate(basis) if row>>i&1) for i in range(n)]
    normalized={0:0}
    for axis in D[-3:]+D[:-3]:
        if axis not in normalized:
            pos=len(normalized)
            normalized.update({k^axis:v^pos for k,v in list(normalized.items())})
    assert [normalized[v] for v in D[-3:]]==[1,2,4]
    return [normalized[v] for v in D[:-3]]
R=realizers(4); lib={}
for p,mask in R.items():
    cols=[v for v in range(1,16) if mask>>(v-1)&1]
    for O in (cols,dual_material(cols)):
        q=calculate(O)
        assert q in valid
        if q not in lib or len(O)<len(lib[q]): lib[q]=O
def obstruct(p):
    missing=[s for i,s in enumerate(small) if not p>>i&1]
    return p.bit_count()>10 and any(len(l)==2 and len(H)==4 and not l<=H for l in missing for H in missing)
assert set(lib)=={p for p in valid if not obstruct(p)}
assert all(calculate(cols)==p and len(cols)<=6 for p,cols in lib.items())
Path(__file__).with_name('single-gadgets.json').write_text(json.dumps(lib,sort_keys=True)+'\n')
print(len(valid),'candidate palettes;',len(R),'rank-four realizations;',len(lib),'all realizable;',len(valid)-len(lib),'excluded; maximal representative size',max(map(len,lib.values())))
