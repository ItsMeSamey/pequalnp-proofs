"""Compute charged floors and explicit twin quotients from public desk titles."""
import argparse,json,re
from functools import reduce
from operator import and_
from pathlib import Path

def groups(profiles):
    return [[i for i,x in enumerate(profiles) if x==p] for p in dict.fromkeys(profiles)]

def classify(title):
    n,m=map(int,re.search(r'(\d+) by (\d+)',title).groups())
    mask=int(re.search(r'mask (\d+)',title)[1])
    cap=int(re.search(r'at most (\d+) gates',title)[1])
    rows=[mask>>(i*m)&((1<<m)-1) for i in range(n)]
    cols=[sum((r>>j&1)<<i for i,r in enumerate(rows)) for j in range(m)]
    minrow,mincol=reduce(and_,rows),reduce(and_,cols)
    rg,cg=groups(rows),groups(cols)
    debit=sum(len(g)-1 for g in rg if rows[g[0]]!=minrow)+sum(len(g)-1 for g in cg if cols[g[0]]!=mincol)
    charged=sum(x!=minrow for x in rows)+sum(y!=mincol for y in cols)
    corner=next(([i,k,j,l] for i in range(n) for k in range(n) if rows[i]!=(1<<m)-1
                for j in range(m) if cols[j]!=(1<<n)-1 and rows[i]&rows[k]&(1<<j)
                for l in range(m) if rows[i] & ~rows[k] & (1<<l)),None)
    floor=charged-1+bool(corner)
    base=[sum(((rows[g[0]]>>h[0])&1)<<j for j,h in enumerate(cg)) for g in rg]
    return dict(mask=mask,cap=cap,charged=charged,corner=corner,floor=floor,row_groups=rg,
                col_groups=cg,charged_debit=debit,unique_rows=base,quotient_cap=cap-debit)
if __name__=='__main__':
    import sys
    board=json.load(open(sys.argv[1]))
    for rid,title in board['gaps']:
        print(rid,json.dumps(classify(title),separators=(',',':')))
