"""Build a local physical instance of the aggregate problem and its pin target."""
from itertools import combinations
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/'unseeded-root-states'))
from solve import image, canonical

def compile_block(real_columns,tags,k,target,ports):
    """Each port is (ordered basis, two imbalance masks, list of probe coordinates).
    Replace its complete set of nonzero virtual directions, all distinct slots.
    """
    cols=list(real_columns)
    scores=list(tags)
    pins=[]
    for U,f,g,probes in ports:
        for coord in range(1,1<<len(U)):
            v=image(U,coord)
            j=coord.bit_length()-1
            color=(((f>>j)&1)|(((g>>j)&1)<<1)) if coord==(1<<j) else 0
            a,b=next((a,b) for a in range(1,4) for b in range(1,4) if a^b==color)
            cols.extend((v,v))
            pins.extend((a,b))
        for x in probes:
            cols.append(image(U,x))
            pins.append(0)
    for i,color in enumerate(pins):
        shift=k+2*i
        scores.append((1<<shift,1<<(shift+1)))
        target^=color<<shift
    return tuple(cols),tuple(scores),target,k+2*len(pins)

def verify():
    from itertools import product
    true=0
    for f,g in product(range(4),repeat=2):
        for P in [(),(1,),(2,),(3,),(1,2)]:
            cols,tags,t,q=compile_block((1,2,3),((1,2),(2,3),(1,1)),2,1,
                                         [((1,2),f,g,P)])
            for c in product(range(4),repeat=3):
                localf=image((1,2,3),sum(((x&1)!=0)<<i for i,x in enumerate(c)))
                localg=image((1,2,3),sum(((x&2)!=0)<<i for i,x in enumerate(c)))
                score=image((1,2,1),sum(((x&1)!=0)<<i for i,x in enumerate(c)))
                score^=image((2,3,1),sum(((x&2)!=0)<<i for i,x in enumerate(c)))
                zero=tuple(a for a,v in zip((1,2,3),c) if not v)
                expected=(localf==f and localg==g and score==1 and
                          len(canonical(zero+P))==len(zero)+len(P))
                pinned=tuple((t>>(2+2*j))&3 for j in range(len(cols)-3))
                expanded=c+pinned
                F=sum(((x&1)!=0)<<i for i,x in enumerate(expanded))
                G=sum(((x&2)!=0)<<i for i,x in enumerate(expanded))
                Z=tuple(a for a,v in zip(cols,expanded) if not v)
                weight=image([a for a,b in tags],F)^image([b for a,b in tags],G)
                actual=(image(cols,F)==image(cols,G)==0 and weight==t and len(canonical(Z))==len(Z))
                assert actual==expected
                true+=actual
    print('5120 pinned local assignments, accepted',true)

if __name__=='__main__':
    verify()
