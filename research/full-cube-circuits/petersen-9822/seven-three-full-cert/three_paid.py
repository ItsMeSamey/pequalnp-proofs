"""Exactly three distinct nonprimitive activations among three conditional switches."""
from pathlib import Path
from two_paid import options,F
def rows():
    root=[F]*4
    for a in options(root):
        mid=root+[a]
        for b in options(mid,[a]):
            pre=mid+[b]
            for c in options(pre,[a,b]):
                yield tuple(pre+[c])
if __name__=='__main__':
    import sys
    p=Path(sys.argv[1])
    with p.open('x') as out:
        for i,row in enumerate(rows(),1):out.write(' '.join(map(str,row))+'\n')
    print(i)
