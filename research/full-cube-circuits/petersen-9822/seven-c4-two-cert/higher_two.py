"""Ordered two-exception activation forests for one to three ordinary roots."""
from pathlib import Path
from two_paid import options,F
from single_paid import walk
from forest3 import forests
from functools import cache
@cache
def representatives(prefix,excluded=()):
    return tuple(options(prefix,excluded))
def templates(p):
    for n0 in range(p,6):
        for n1 in range(1,7-n0):
            for ordinary in forests(n0):
                if len(ordinary)!=p:continue
                for first in forests(n1):
                    for last in forests(7-n0-n1):
                        yield ordinary,first,last
def generate(p):
    rows=set()
    for ordinary,first,last in templates(p):
        pre=walk(ordinary,[F]*p,0)
        for u in representatives(tuple(pre)):
            mid=pre+walk(first,[u]*len(first),len(pre))
            for v in representatives(tuple(mid),(u,)):
                rows.add(tuple(mid+walk(last,[v]*len(last),len(mid))))
    return sorted(rows)
if __name__=='__main__':
    import sys
    p=int(sys.argv[1]);dest=Path(sys.argv[2])
    rows=generate(p)
    with dest.open('x') as f:
        for row in rows:f.write(' '.join(map(str,row))+'\n')
    print(len(rows))
