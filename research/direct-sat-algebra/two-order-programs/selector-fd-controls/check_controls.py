"""Fresh original-CNF controls for independent prefix and suffix widths."""
from itertools import product
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-proxy-native'))
from proxy import solve_cnf, recode
from coset import kernel,tail_equations

def source(m,kind):
    for i in range(m):
        s,w=i+1,m+1
        x,y,a,b=[t*m+2+i for t in (1,2,3,4)]
        if kind=='frozen':
            rows=[(-s,x),(s,-x),(s,a,b),(w,x,y)]
        else:
            rows=[(s,x,a)]
            for bits in product((0,1),repeat=3):
                if sum(bits)%2:
                    rows.append(tuple(-v if bit else v for bit,v in zip(bits,(w,x,y))))
        for row in rows:
            yield iter(row)

def verify(m,kind):
    n=5*m+1
    rows=[tuple(c) for c in source(m,kind)]
    rec,original,data,masters,copies=recode(n,rows)
    assert masters==list(range(1,m+2)) and not copies
    front=[original[m+2+i] for i in range(m)]
    late=[c for c in rec if m+1 in map(abs,c)]
    equations=tail_equations(late,fixed=range(1,m+1))
    projected=[sum(((u>>(v-1))&1)<<i for i,v in enumerate(front)) for u in kernel(n,equations)]
    images={0}
    for u in projected:images|={v^u for v in images}
    assert len(images)==(1 if kind=='frozen' else 2**m)
    for cap in (2**m-1,2**m):
        r=solve_cnf(n,source(m,kind),state_cap=cap)
        expected='skip' if kind=='frozen' and cap<2**m else 'sat'
        assert r['status']==expected
        print(m,kind,cap,r['status'],r['cost']['stream']['highwater'])
if __name__=='__main__':
    for m in (2,3,4):
        for kind in ('frozen','free'):verify(m,kind)
