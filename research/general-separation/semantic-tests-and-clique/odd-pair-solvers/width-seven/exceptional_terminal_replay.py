"""Quotient root enumeration by S4 x S3; independent terminal enumeration."""
from collections import Counter
from itertools import combinations, permutations
from types import SimpleNamespace
from single_leaf_raw_terminal_replay import terminal
from degree_five_active_shells import root,key,glue
from single_leaf_high_pin_shells import grow
from edge_torso_atlas_check import witnesses


def starts():
    sites = range(2,9)
    pairs=list(combinations(sites,2))
    actions=[]
    for a in permutations(range(2,6)):
        for c in permutations(range(6,9)):
            perm=(0,1)+a+c
            bits=[1<<pairs.index(tuple(sorted((perm[i],perm[j])))) for i,j in pairs]
            chunks=[]
            for lo in (0,7,14):
                table=[0]*128
                for h in range(1,128):
                    t=h&-h
                    table[h]=table[h^t]|bits[lo+t.bit_length()-1]
                chunks.append(table)
            actions.append(chunks)
    seen=bytearray(1<<21)
    for code in range(len(seen)):
        if seen[code]:continue
        orbit={a[code&127]|b[(code>>7)&127]|c[code>>14] for a,b,c in actions}
        for h in orbit:seen[h]=1
        rows=[448,508,2,2,2,2,3,3,3]
        for pos,(i,j) in enumerate(pairs):
            if code>>pos&1:
                rows[i]|=1<<j
                rows[j]|=1<<i
        if any(r.bit_count()>5 for r in rows[2:]) or any(r.bit_count() not in (3,5) for r in rows[6:]):
            continue
        ports=[i for i in range(2,6) if rows[i].bit_count()<5]
        d,t=root(dict(rows=rows,ports=ports))
        if ports and not t[0]:yield d,t,rows,ports,len(orbit)


def run(roots,budget):
    q=[(*r,budget) for r in roots]
    counts=Counter()
    while q:
        nxt=[]
        cache={}
        for d,t,rows,ports,weight,b in q:
            token=(key(d,t),b)
            if token not in cache:
                k=len(d);f=(1<<k)-1
                drift=sum((1^(x%2))<<j for j,x in enumerate(d))
                ok=[]
                for v,row in enumerate(t):
                    entries=[]
                    for u,m in row.items():
                        full=(u==f and v==drift)
                        if full:entries.append((f,u))
                        if m>int(full):entries.append((0,u))
                    ok.append(entries)
                old=SimpleNamespace(rows=[0]*k,ports=range(k),degrees=d,ok=ok)
                cache[token]=list(terminal(old,b)),list(grow(d,t,b))
            ends,extensions=cache[token]
            for inc,ext in ends:
                rr,_=glue(rows,ports,inc,ext)
                assert witnesses(rr,0,1) and sum(r.bit_count()==1 for r in rr)==budget
                counts[len(rr)]+=weight
            for dd,tt,inc,ext,bb in extensions:
                rr,j=glue(rows,ports,inc,ext)
                nxt.append((dd,tt,rr,j,weight,bb))
        print('budget',budget,'prefixes',sum(r[-2] for r in q),'terminals',dict(counts),flush=True)
        q=nxt
    assert counts=={10:576}


if __name__=='__main__':
    roots=list(starts())
    for budget in (0,1):run(roots,budget)
