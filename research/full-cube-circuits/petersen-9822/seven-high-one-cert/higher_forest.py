from pathlib import Path
from forest3 import forests
from single_paid import walk,F
from two_paid import options

def generate(p):
    classes=[set(),set()]
    for forest in forests(7):
        if len(forest)==p:classes[0].add(tuple(walk(forest,[F]*p,0)))
    for ordinary_size in range(p,7):
        for ordinary in forests(ordinary_size):
            if len(ordinary)!=p:continue
            prefix=walk(ordinary,[F]*p,0)
            for u in options(prefix):
                for specials in forests(7-ordinary_size):
                    suffix=walk(specials,[u]*len(specials),ordinary_size)
                    classes[1].add(tuple(prefix+suffix))
    return classes
if __name__=='__main__':
    import sys
    for p in (3,2,1):
        for h,rows in enumerate(generate(p)):
            print('conditional',7-p,'distinct',h,'profiles',len(rows))
            if len(sys.argv)>1:
                Path(sys.argv[1],f'c{7-p}-w{h}.tsv').write_text(''.join(' '.join(map(str,r))+'\n' for r in sorted(rows)))
