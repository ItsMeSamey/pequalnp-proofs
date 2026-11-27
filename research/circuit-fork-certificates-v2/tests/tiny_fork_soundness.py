"""Finite DAG oracle for first-fork necessary conditions. Run with python -BO."""
from collections import Counter, defaultdict
from itertools import combinations
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def generate(n, length, gates=()):
    if len(gates) == length:
        yield gates
        return
    m = n + len(gates)
    for a in range(m):
        yield from generate(n, length, gates + (('!', a),))
        for b in range(a+1, m):
            for op in '&|':
                yield from generate(n, length, gates + ((op,a,b),))


def wires(n, gates, pattern):
    bits = [(pattern >> j) & 1 for j in range(n)]
    for op, *p in gates:
        if op == '!':
            bits.append(1-bits[p[0]])
        elif op == '&':
            bits.append(bits[p[0]] & bits[p[1]])
        else:
            bits.append(bits[p[0]] | bits[p[1]])
    return bits


def corners(care,j,k):
    allowed = set(range(4))
    mask = (1<<j) | (1<<k)
    fibers = defaultdict(list)
    for x,y in care.items():
        fibers[x & ~mask].append((((x>>j)&1) + 2*((x>>k)&1), y))
    for points in fibers.values():
        allowed = {c for c in allowed if any(all(((t>>x)&1)==y for x,y in points)
            for t in [0,15,10,5,12,3,1<<c,15^(1<<c)])}
    return allowed


def check(n,gates,counts,observer=None):
    nxt = [[] for _ in range(n+len(gates))]
    for i,g in enumerate(gates,n):
        for v in g[1:]:
            nxt[v].append(i)
    if not all(nxt[:-1]):
        return
    counts['live circuits'] += 1
    values = [wires(n,gates,x) for x in range(1<<n)]
    for sampled in [False,True]:
        care = {x:v[-1] for x,v in enumerate(values) if not sampled or (x+len(gates))%5}
        dirs = [{care[x] for x in care if not x & (1<<i) and
                 care.get(x | (1<<i)) == 1-care[x]} for i in range(n)]
        if not all(dirs):
            continue
        counts['sampled' if sampled else 'complete'] += 1
        groups = defaultdict(dict)
        outside = 0
        for i,ds in enumerate(dirs):
            if len(ds)<2:
                outside |= 1<<i
                continue
            f=i
            neg=0
            while len(nxt[f])==1:
                f=nxt[f][0]
                neg ^= gates[f-n][0]=='!'
            require(len(nxt[f])>=2, 'binate input without fork')
            groups[f][i]=neg
        if observer is not None:
            observer(care,n,gates,groups,outside)
        counts['groups']+=len(groups)
        for f,group in sorted(groups.items()):
            mask=sum(1<<j for j in group)
            sign=sum(v<<j for j,v in group.items())
            for j,k in combinations(group,2):
                permitted=corners(care,j,k)
                require(permitted,'signed pair shape')
                if group[j]==group[k]:
                    require(permitted & {0,3},'uniform pair shape')
                counts['pairs']+=1
            for x,y in combinations(care,2):
                if (x^y)&outside:
                    continue
                a,b=(x^sign)&mask,(y^sign)&mask
                u,v=values[x][f],values[y][f]
                require(not(a&b==a and u>v or a&b==b and v>u),'ordered orientation')
                if not (x^y)&~mask and care[x]!=care[y]:
                    require(u!=v,'fork omitted a required distinction')
            outside |= mask
    return True


def run(observer=None):
    counts=Counter()
    for n,length in [(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)]:
        for gates in generate(n,length):
            counts['generated']+=1
            check(n,gates,counts,observer)
    targets=[
        (3,(('&',0,1),('|',3,2),('&',3,2),('!',5),('&',4,6))),
        (3,(('!',0),('&',3,1),('|',4,2),('&',4,2),('!',6),('&',5,7))),
        (3,(('|',0,1),('&',0,1),('!',4),('&',3,5),('|',6,2),('&',6,2),('!',8),('&',7,9))),
        (4,(('|',0,1),('&',0,1),('!',5),('&',4,6),('|',2,3),('&',2,3),('!',9),('&',8,10),('|',7,11)))]
    for n,gates in targets:
        require(check(n,gates,counts,observer),'dead target fixture')
    # Enumerate every input sign assignment for two multi-leaf fork groups.
    base=(('&',0,1),('|',2,3),('|',4,5),('&',4,5),('!',7),('&',6,8))
    for flips in range(16):
        renamed=list(range(4))
        prefix=[]
        for j in range(4):
            if flips & (1<<j):
                prefix.append(('!',j))
                renamed[j]=3+len(prefix)
        for op,*args in base:
            prefix.append((op,*(renamed[j] for j in args)))
            renamed.append(3+len(prefix))
        require(check(4,tuple(prefix),counts,observer),'dead phased target')
    require(not corners({0:0,1:1,2:1,3:0},0,1),'xor wrongly admitted')
    require(corners({0:0,1:0,2:0,3:1},0,1)=={3},'false corner admitted')
    return dict(counts)

if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True))
