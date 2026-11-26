"""Check coverage of p=3 incidence models emitted by quartet_models."""
from pathlib import Path
import sys
def canonical(p,g,c,b,q,d):
    assert p==3 and q==d==0 and c|b==7 and not c&b
    edges=[(i,j) for i in range(3) for j in range(i) if g>>(i*(i-1)//2+j)&1]
    if b==7:return 'all',len(edges)
    priv=[i for i in range(3) if not b>>i&1]
    assert len(priv)==1
    return 'private',len(edges),sum(priv[0] in e for e in edges)
if __name__=='__main__':
    data=[tuple(map(int,l.split())) for l in Path(sys.argv[1]).read_text().splitlines() if l.strip()]
    shapes={canonical(*r) for r in data if r[0]==3}
    assert shapes=={('all',0),('all',1),('all',2),('all',3),('private',2,2),('private',3,2)}
    print('all four all-branching graphs and both private shapes',flush=True)
