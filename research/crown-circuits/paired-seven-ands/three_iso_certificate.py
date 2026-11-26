"""Recover explicit gate permutations and pin flips for each physical transfer."""
from itertools import permutations
from pathlib import Path
from three_isomorphic import load


def mapping(t,target):
    for p in permutations(range(3)):
        for terminals in permutations(range(3,7)):
            perm=p+terminals
            flips=[]
            for j,k in enumerate(perm):
                column=tuple((t[i]>>(2*j))&3 for i in range(3))
                wanted=tuple((target[p[i]]>>(2*k))&3 for i in range(3))
                if column==wanted:flips.append(0)
                elif tuple(((v&1)<<1)|(v>>1) for v in column)==wanted:flips.append(1)
                else:break
            if len(flips)!=7:continue
            for i,m in enumerate(t):
                image=sum(1<<(2*perm[j]+(b^flips[j])) for j in range(7) for b in (0,1) if m>>(2*j+b)&1)
                assert image==target[p[i]]
            return list(perm),flips
    raise ValueError((t,target))


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('catalog',type=Path)
    parser.add_argument('transfer',type=Path)
    args=parser.parse_args()
    t={r[0]:r[1:4] for r in load(args.catalog)}
    for line in args.transfer.read_text().splitlines():
        i,source,j=line.split()
        p,f=mapping(t[int(i)],t[int(j)])
        print(i,source,j,*p,*f)
