"""Every feasible eight-line boundary contains all seven singleton signatures."""
from pathlib import Path
import json,sys
base=Path(__file__).resolve().parent/'irreducible-ten'/'source'
sys.path.insert(0,str(base))
from verify_packing import samples
rows,f,t=samples(base/'L-meta-18968.json')
coords=lambda k: (rows[k]&8191,rows[k]>>13&127)
pp={coords(i) for i in range(676) if (t^f)>>i&1}
nn={coords(i) for i in range(676) if not t>>i&1}
rels={(l,k) for p,l in pp for n,k in nn if not p&~n}
rels=sorted((l,k) for l,k in rels if not any(l==v and k!=w and not k&~w for v,w in rels))
pairs=json.loads((base/'pairs.json').read_text())['line']
init=[(coords(p)[1],coords(n)[1]) for p,n in pairs]+[(0,0)]
visits=0
def possible(slots,omit):
    global visits
    visits+=1
    while True:
        old=slots[:]; choice=None
        for i,(inside,outside) in enumerate(slots):
            if inside&~omit or outside&omit:continue
            free=127&~(inside|outside)
            if not free:return False
            if free.bit_count()==1:
                slots[i]=(inside,outside|free) if omit&free else (inside|free,outside)
        for a,b in rels:
            eligible=[i for i,(x,y) in enumerate(slots) if not (x&b or y&a)]
            if not eligible:return False
            if any(not a&~slots[i][0] and not b&~slots[i][1] for i in eligible):continue
            if len(eligible)==1:
                i=eligible[0];x,y=slots[i];slots[i]=x|a,y|b
            elif choice is None or len(eligible)<choice[0]:
                i=eligible[0];x,y=slots[i];free=(a|b)&~(x|y)
                choice=(len(eligible),i,free&-free)
        if slots==old:break
    if choice:_,i,bit=choice
    else:
        for i,(x,y) in enumerate(slots):
            free=127&~(x|y)
            if free:bit=free&-free;break
        else:return True
    x,y=slots[i];copy=slots[:];copy[i]=x|bit,y
    slots[i]=x,y|bit
    return possible(copy,omit) or possible(slots,omit)
for j in range(7):
    assert not possible(init[:],1<<j)
print('All eight-line bases include seven singleton line signatures;',visits,'states.')
