"""Exactly one exceptional degree-seven pin, sharing every neighbor of the degree-three pin."""
from collections import Counter
from itertools import combinations
from degree_five_active_shells import root,key,glue,parity
from single_leaf_high_pin_shells import grow,terminals


def starts():
    n=9
    exclusive=range(2,6)
    common=range(6,9)
    rows=[0]*n
    def toggle(i,j):
        rows[i]^=1<<j
        rows[j]^=1<<i
    for v in common:
        toggle(0,v)
    for v in range(2,9):
        toggle(1,v)
    edges=list(combinations(range(2,9),2))
    def visit(k):
        if k==len(edges):
            if all(rows[v].bit_count() in (3,5) for v in common):
                yield tuple(rows),[v for v in exclusive if rows[v].bit_count()<5]
            return
        i,j=edges[k]
        yield from visit(k+1)
        if max(rows[i].bit_count(),rows[j].bit_count())<5:
            toggle(i,j)
            yield from visit(k+1)
            toggle(i,j)
    yield from visit(0)


def only_full(rows):
    f=(1<<len(rows))-1
    return all(r.bit_count()%2 for r in rows) and not any(all(
        not(s>>j&1) or parity(r&s) for j,r in enumerate(rows)) for s in range(3,f,4))


def main(budget):
    queue=[];examples={};counts=Counter()
    def record(rows):
        assert only_full(rows) and sum(r.bit_count()==1 for r in rows)==budget
        counts[len(rows)]+=1
        examples.setdefault(len(rows),tuple(rows))
    for rows,ports in starts():
        d,t=root(dict(rows=rows,ports=ports))
        if t[0]:
            if sum(r.bit_count()==1 for r in rows)==budget and only_full(rows):record(rows)
        else:
            if ports:queue.append((d,t,rows,ports,budget))
    print('closed',dict(counts),flush=True)
    while queue:
        levels={};end={};later=[]
        cap=max(len(rows)+sum(5-x for x in d) for d,t,rows,ports,b in queue)
        for d,t,rows,ports,b in queue:
            token=key(d,t),b
            if token not in levels:
                levels[token]=list(grow(d,t,b));end[token]=list(terminals(d,t,b))
            for inc,ext in end[token]:record(glue(rows,ports,inc,ext)[0])
            for dd,tt,inc,ext,bb in levels[token]:
                graph,newports=glue(rows,ports,inc,ext)
                later.append((dd,tt,graph,newports,bb))
        print('prefixes',len(queue),'states',len(levels),'cap',cap,'cumulative labelled',dict(counts),flush=True)
        queue=later
    print('examples',examples,flush=True)


if __name__=='__main__':
 for budget in (0,1):main(budget)
