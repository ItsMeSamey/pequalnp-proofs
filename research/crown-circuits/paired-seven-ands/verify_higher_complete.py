"""Verify every finite-search ledger and analytical partition for a dirty-count stratum."""
from pathlib import Path
from collections import Counter, defaultdict
import gzip
import argparse

def rows(path):
    mode=gzip.open if path.suffix=='.gz' else open
    with mode(path,'rt') as src:
        for line in src:
            assert line.endswith('\n')
            yield list(map(int,line.split()))

def verify(d,cat,projection,cycles,one,full):
    projected={}
    if projection:
        for i,c,cap,ports in rows(projection):projected[i]=(c,cap,ports)
    need=defaultdict(set);hist=Counter();cnt=0
    for i,c,cap,*t in rows(cat):
        assert i==cnt and len(t)==d;cnt+=1
        if projection:
            cc,n,p=projected[i];assert (cc,n)==(c,cap)
        else:p=2
        u=0
        for m in t:u|=m
        e=sum(not(u>>(2*j)&3) for j in range(d))
        if cap<12:key='capacity'
        elif p<2:key='signed_port'
        elif e+c>5:key='too_many_pins'
        elif c==3 and e==2:key='two_cycle'
        elif c==3:
            assert e==1;key='two_tag_shape';need[key].add(i)
        elif e+c==5:key='matching';need[key].add(i)
        else:key=f'full{c}';need[key].add(i)
        hist[c,key]+=1
    if projection:assert len(projected)==cnt
    for key,path in [('two_tag_shape',one),('matching',cycles)]+[(f'full{c}',p) for c,p in enumerate(full)]:
        rr=list(rows(path));idx={r[0] for r in rr};assert idx==need[key],(key,len(idx),len(need[key]),sorted(need[key]-idx)[:12])
        assert len(rr)==len(idx) and all(r[-1]==0 for r in rr),key
    for c in range(4):print(c,{k:n for (cost,k),n in sorted(hist.items()) if cost==c})
    print('Verified',cnt,'physical templates at dirty count',d)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('dirty',type=int);p.add_argument('catalog',type=Path)
    p.add_argument('cycles',type=Path);p.add_argument('one_earliest',type=Path)
    p.add_argument('full',nargs=3,type=Path);p.add_argument('--projection',type=Path)
    a=p.parse_args();verify(a.dirty,a.catalog,a.projection,a.cycles,a.one_earliest,a.full)
