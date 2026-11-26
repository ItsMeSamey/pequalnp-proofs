from itertools import combinations, product
from math import comb


def twin_classes(n, edges):
    groups = []
    neighborhoods = [set() for _ in range(n)]
    for x,y in edges:
        neighborhoods[x].add(y)
        neighborhoods[y].add(x)
    for v in range(n):
        for group in groups:
            w = group[0]
            if neighborhoods[v]-{w} == neighborhoods[w]-{v}:
                group.append(v)
                break
        else:
            groups.append([v])
    return groups


def verify(n, edges):
    groups = twin_classes(n, edges)
    direct = [1]+[0]*((1<<n)-1)
    for u,v in edges:
        mask = (1<<u)|(1<<v)
        direct = [3*x+direct[s^mask] for s,x in enumerate(direct)]
    for b in range(1<<n):
        total = 0
        for profile in product(*(range(len(g)+1) for g in groups)):
            sign = 1
            sel = set()
            for g,k in zip(groups,profile):
                t = sum((b>>v)&1 for v in g)
                sign *= sum((-1)**j*comb(t,j)*comb(len(g)-t,k-j)
                            for j in range(max(0,k-len(g)+t),min(k,t)+1))
                sel.update(g[:k])
            cut = sum((u in sel)!=(v in sel) for u,v in edges)
            total += sign << (2*len(edges)-cut)
        assert total == direct[b]*(1<<n)
    return 1<<n


if __name__ == '__main__':
    cases = 0
    for n in range(1,5):
        pairs = list(combinations(range(n),2))
        for bits in range(1<<len(pairs)):
            cases += verify(n,[e for j,e in enumerate(pairs) if (bits>>j)&1])
    print(cases, 'graph/syndrome cases passed')
