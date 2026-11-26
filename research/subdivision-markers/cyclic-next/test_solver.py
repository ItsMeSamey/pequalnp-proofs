from random import Random
from solver import solve

def check(guards, labels, tree):
    def value(x):
        acc = 0
        for i,g in enumerate(guards):
            if x >> i & 1:
                if not any(((x&mask).bit_count()%2) ^ c for mask,c in g):
                    return None
                acc ^= labels[i]
        return acc
    expected = {value(x) for x in range(1 << len(guards))} - {None}
    witnesses = solve(guards,labels,tree)
    assert expected == witnesses.keys()
    assert all(value(x) == z for z,x in witnesses.items())

if __name__ == '__main__':
    rng = Random(7231)
    for _ in range(600):
        n = rng.randint(1,9)
        guards = [[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))] for i in range(n)]
        labels = [rng.randrange(8) for i in range(n)]
        nodes = list(range(n))
        rng.shuffle(nodes)
        while len(nodes) > 1:
            a = nodes.pop(rng.randrange(len(nodes)))
            b = nodes.pop(rng.randrange(len(nodes)))
            nodes.append((a,b))
        check(guards, labels, nodes[0])
    n = 80
    full = (1<<n)-1
    guards = [[(full,1)] for _ in range(n)]
    labels = [1 << (i%4) for i in range(n)]
    nodes = list(range(n))
    while len(nodes)>1:
        nodes = [(nodes[i],nodes[i+1]) if i+1<len(nodes) else nodes[i] for i in range(0,len(nodes),2)]
    hits = solve(guards, labels, nodes[0])
    assert set(hits) == {z for z in range(16) if not z.bit_count()%2}
    print('600 random instances, all marker outputs and witnesses; dense 80-variable cyclic example')
