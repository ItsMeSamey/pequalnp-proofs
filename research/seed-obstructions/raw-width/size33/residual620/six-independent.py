"""Direct six-ID audit, with no n23/site6 census or orbit substitution."""
from pathlib import Path
from itertools import combinations, product, combinations_with_replacement
import ast
import json
import os
import sys

base = Path('/workspace/scratch')
pivot = base/'synthesis_new/t0-pivot-clean'
fivepath = base/'syn_bounds/s33-low/all23-low'
rolepath = base/'syn_quotients/active74'
os.environ['LOW_WIDTH']='23'
sys.path.insert(0,str(fivepath))
import route5, five
from pairs import classify
from spec import bank, Rbank
from input import raw_samples
sys.path.insert(0,str(rolepath))
from realcore import Source, ALL, pass_budget
from cuts import load

selected = {567:(395,6),645:(473,12),771:(599,46),
            776:(604,12),822:(650,6),931:(759,46)}
records = {}
for i,t,_,r,c in map(json.loads,(pivot/'remaining.jsonl').read_text().splitlines()):
    if t == 0 and i in selected:
        assert i not in records and r==8191 and len(c)==3
        records[i] = tuple(c)
assert records.keys()==selected.keys()
force = {i: sum(1<<u for q,u,chart in ast.literal_eval(line))
         for i,line in ((int(t),x) for t,x in
             (line.split(' ',1) for line in (pivot/'receipt.log').read_text().splitlines()))}
s=object.__new__(Source);s.P,s.N=load(());s.pts=ALL
s.stars=tuple({x&8191 for x in s.P if x>>(13+j)&1} for j in range(7))
s.inc={p:sum(1<<j for j,t in enumerate(s.stars) if p in t) for p in ALL}
assert all(len(t)==4 for t in s.stars)
def packbudget(ds,b):
    # For the six rows the only nonnegative spare amounts are zero, one and two.
    if b<0:return False
    assert b<=2
    options=[]
    for k in range(1,b+1):
        for C in combinations(range(8),k+1):
            m=sum(1<<j for j in C)
            options.append((k,{i for i,d in enumerate(ds) if (d&m).bit_count()>=2}))
        if k==1:
            options.extend((1,{i}) for i in range(len(ds)))
    needed=set(range(len(ds)))
    if not needed:return True
    if any(z>=needed for _,z in options):return True
    return b==2 and any(x|y>=needed for (a,x),(b,y) in combinations(options,2) if a+b<=2)
def independent_rank_bill(p, neg_masks, distinct_physical_reads):
    # Independently allow one or two sets of row-points per label occurrence.
    pool=range(1,1<<len(p))
    for masks in combinations_with_replacement(pool,distinct_physical_reads):
        use={0,*masks}
        if len(masks)==2 and not masks[0]&masks[1]:use.add(masks[0]|masks[1])
        if all(any(w&m==w and not m&v for m in use) for w,v in neg_masks):
            return True
    return False
for i,c in records.items():
    idx,k=selected[i]
    assert force[i]==k
    matches=[j for j in range(len(bank)) if set(Rbank(j))==set(ALL)|set(c)]
    assert matches==[idx]
    s.bank(c,0)
    feasible=[]
    for o in range(128):
        if (o&k)!=k:continue
        _,m,solo,b=s.roles(o,11)
        val=packbudget(solo,b)
        assert val==pass_budget(solo,b)
        if val:feasible.append(o)
    print(i,'bank',idx,'required ordinary mask',k,'budget survivors',feasible)
    if i in (771,931):
        assert not feasible
        continue
    assert feasible==[k]
    O=tuple(t for t in range(7) if (1<<t)&k)
    assert classify(O,idx)=='binary' and route5.check(idx,O)==0
    owners,A,M,dests=five.domain(O)
    exterior={n for n in five.N if all(n&five.stars[t] for t in O)}
    def needs(u,p):
        return A.get((u,p)) and all(v==u or any(n&five.stars[v] for n in five.masks[u,p]) for v in owners)
    count=0
    for assign,_ in five.cases(O):
        count+=1
        rejected=False
        for u in owners:
            total=0
            for v in (*owners,7):
                points=[p for p in M if assign[p]==v]
                rs=[p for p in points if needs(u,p)]
                if v==u or not rs:continue
                neg=set(exterior if v==7 else (n for n in five.N if n&five.stars[v]))
                for p in points:neg.update(M[p])
                rows={(sum(1<<j for j,p in enumerate(rs) if n&p),
                       sum(1<<j for j,p in enumerate(rs) if n in M[p])) for n in neg}
                total+=next((h for h in (1,2) if independent_rank_bill(rs,rows,h)),3)
            if total>2:
                rejected=True; break
        assert rejected
    print('  holder maps',count,'all exceed two physical outputs')
    assert count==14
