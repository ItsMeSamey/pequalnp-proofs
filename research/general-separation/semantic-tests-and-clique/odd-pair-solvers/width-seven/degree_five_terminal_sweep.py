"""Exact terminal census of 3-connected inclusion-minimal odd supports with named pins."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

from degree_five_raw_shell_check import Raw, expand, grow, ones


def three_connected(rows):
    n = len(rows)
    if n < 4:
        return False
    for i,j in combinations(range(n),2):
        live = ((1 << n)-1) ^ (1 << i) ^ (1 << j)
        reached = live & -live
        queue = reached
        while queue:
            bit = queue & -queue
            queue ^= bit
            fresh = rows[bit.bit_length()-1] & live & ~reached
            reached |= fresh
            queue |= fresh
        if reached != live:
            return False
    return True


def exact_word(rows):
    full = (1 << len(rows))-1
    for s in range(3,full,4):
        if s.bit_count()%2 == 0 and all((rows[i]&s).bit_count()%2 for i in ones(s)):
            return False
    return all(r.bit_count() in (3,5) for r in rows)


def closed_root(c,a,b):
    # Add in fixed color order; every intermediate successful word is proper.
    if (2+a+b+c)%2:
        return
    colors = [1]*a + [2]*b + [3]*c
    rows = [0,0]
    def add(i):
        if i == len(colors):
            if exact_word(rows) and three_connected(rows):
                yield tuple(rows)
            return
        tag = colors[i]
        force = tag | sum(1 << (j+2) for j,prev in enumerate(colors[:i])
                          if (tag,prev) in ((1,2),(2,1)))
        optional = [j for j in range(2,len(rows)) if not (force >> j & 1)]
        for mask in range(1 << len(optional)):
            adj = force | expand(mask, optional)
            if adj.bit_count()>5 or any(rows[j].bit_count()>=5 for j in ones(adj)):
                continue
            pos=len(rows)
            for j in ones(adj):
                rows[j] |= 1 << pos
            rows.append(adj)
            rem=len(colors)-i-1
            if all(r.bit_count()+rem>=3 for r in rows) and (
                not rem or not any(all((rows[j]&s).bit_count()%2 for j in ones(s))
                                   for s in range((1 << pos)+3,1 << (pos+1),4))):
                yield from add(i+1)
            rows.pop()
            for j in ones(adj):
                rows[j] ^= 1 << pos
    yield from add(0)


def terminal(old):
    n=len(old.rows)
    ports=old.ports
    old_full=(1 << n)-1
    responses=[set((w==old_full,u) for w,u in entries) for entries in old.ok]
    full_ports=(1 << len(ports))-1
    from itertools import product
    all_types=range(1,full_ports+1)
    singleton_ok={t for t in all_types if not any((t&u).bit_count()%2 for _,u in responses[t])}
    pair_choices={}
    for t,h in product(all_types,repeat=2):
        bad={1^((t&u).bit_count()%2) for _,u in responses[t^h]
             if ((t&u).bit_count()^(h&u).bit_count())%2==0}
        pair_choices[t,h]={0,1}-bad
    def finish(ts):
        m=len(ts)
        sig=[0]*(1 << m)
        for s in range(1,len(sig)):
            bit=s&-s
            sig[s]=sig[s^bit]^ts[bit.bit_length()-1]
        # All old vertices must in particular work with the full new layer.
        if (True,full_ports) not in responses[sig[-1]]:
            return
        rr=[0]*m
        opts=[]
        for i,j in combinations(range(m),2):
            choices=pair_choices[ts[i],ts[j]] if m>2 else {0,1}
            if not choices:
                return
            if choices=={1}:
                rr[i]|=1 << j
                rr[j]|=1 << i
            elif len(choices)==2:
                opts.append((i,j))
        def choose(k):
            ds=[t.bit_count()+r.bit_count() for t,r in zip(ts,rr)]
            if max(ds)>5: return
            if k<len(opts):
                i,j=opts[k]
                yield from choose(k+1)
                rr[i]^=1 << j
                rr[j]^=1 << i
                yield from choose(k+1)
                rr[i]^=1 << j
                rr[j]^=1 << i
                return
            if any(d not in (3,5) for d in ds):return
            for s,v in enumerate(sig):
                for full,u in responses[v]:
                    if (not full or s!=len(sig)-1) and all(
                        ((u&ts[j]).bit_count()+(s&rr[j]).bit_count())%2 for j in ones(s)):
                        return
            rows=list(old.rows)+[expand(t,ports)|(r << n) for t,r in zip(ts,rr)]
            for j,t in enumerate(ts,n):
                for h in ones(t):
                    rows[ports[h]] |= 1 << j
            if three_connected(rows):
                assert exact_word(rows)
                yield tuple(rows)
        yield from choose(0)
    def choose_types(left,ts,lo):
        if not any(left):
            if ts: yield from finish(ts)
            return
        for t in range(lo,full_ports+1):
            if len(ts)>=1 and (t not in singleton_ok or ts[0] not in singleton_ok):
                continue
            if len(ts)>=2 and (any(not pair_choices[t,h] for h in ts)
                               or not pair_choices[ts[0],ts[1]]):
                continue
            diff=tuple(v-(t>>i&1) for i,v in enumerate(left))
            if min(diff)>=0:
                yield from choose_types(diff,ts+[t],t)
    for ds in product(*[[total-d for total in (3,5) if total>=d] for d in old.degrees]):
        if sum(v>0 for v in ds)>=3:
            yield from choose_types(ds,[],1)


def main():
    data=json.loads(Path(__file__).with_name('degree_five_common_core_census.json').read_text())
    counts=Counter()
    examples={}
    def record(graphs):
        for rows in graphs:
            n=len(rows)
            counts[n]+=1
            examples.setdefault(n,rows)
    for group in data:
        record(closed_root(group['c'],group['a'],group['b']))
    print('after closed roots',sorted(counts.items()),flush=True)
    states=[]
    for group in data:
        for r in group['orbits']:
            if r['all_pieces_reach_port']:
                rows=r['rows']
                ports=[i for i,v in enumerate(r['exterior_degrees'],2) if max(v)>0]
                states.append(Raw(rows,ports,range(3,1 << len(rows),4)))
    while states:
        print('physical prefixes',len(states),flush=True)
        for st in states:
            record(terminal(st))
        print('cumulative',sorted(counts.items()),flush=True)
        states=[child for st in states for child in grow(st)]
    print('one pin-labelled adjacency example per order',examples,flush=True)


if __name__=='__main__':
    main()
