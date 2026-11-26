from itertools import product
from random import Random

def count(n, clauses, pins=()):
    return sum(all(x[v] == b for v, b in pins) and
               all(any(x[v] == b for v, b in c) for c in clauses)
               for x in product((0, 1), repeat=n))

def port_table(n, clauses, ports):
    d = len(ports)
    tab = [count(n, clauses, [p for i in range(d) if m >> i & 1 for p in ports[i]])
           for m in range(1 << d)]
    for i in range(d):
        for m in range(1 << d):
            if not m >> i & 1:
                tab[m] -= tab[m | (1 << i)]
    return tab

def path_count(n, f, ports):
    msg = {1: 1}
    for i, local in enumerate(f):
        # Left and right ports at endpoints include harmless empty dummy ports.
        tab = port_table(n, local, ports[i])
        msg = {r: sum(v * tab[l + 2*r] for prev, v in msg.items()
                      for l in (0, 1) if prev or l) for r in (0, 1)}
    return sum(msg.values())

def check(seed):
    rng = Random(seed)
    n, blocks = 2, 4
    pin = lambda: (rng.randrange(n), rng.randrange(2))
    f = [[tuple(pin() for _ in range(2)) for _ in range(rng.randrange(3))]
         for _ in range(blocks)]
    ports = [[tuple(pin() for _ in range(rng.randrange(4))) for _ in range(2)]
             for _ in range(blocks)]
    ports[0][0] = ports[-1][1] = ()
    full = [tuple((v+n*i, b) for v,b in c) for i in range(blocks) for c in f[i]]
    for i in range(blocks-1):
        full.extend(((v+n*i,b),(w+n*(i+1),c)) for v,b in ports[i][1]
                    for w,c in ports[i+1][0])
    assert path_count(n,f,ports) == count(n*blocks,full)

def hcheck(seed):
    rng = Random(seed)
    def build(lo, hi):
        if hi-lo == 2:
            f = [[(rng.randrange(lo,hi),rng.randrange(2)) for _ in range(2)]]
            def solve(p):
                return count(2, [[(v-lo,b) for v,b in f[0]]],
                             [(v-lo,b) for v,b in p])
            return f, solve
        mid=(lo+hi)//2
        lf,L = build(lo,mid)
        rf,R = build(mid,hi)
        a=[(v,rng.randrange(2)) for v in range(lo,mid)]
        b=[(v,rng.randrange(2)) for v in range(mid,hi)]
        def solve(p):
            pl=[t for t in p if t[0]<mid]
            pr=[t for t in p if t[0]>=mid]
            u,up,v,vp=L(pl),L(pl+a),R(pr),R(pr+b)
            return up*v+u*vp-up*vp
        return lf+rf+[[x,y] for x in a for y in b],solve
    f,solve=build(0,8)
    assert solve([])==count(8,f)

for seed in range(200):
    check(seed)
    hcheck(seed)
print("200 signed path tests and 200 signed hierarchy tests agree with exhaustive #SAT.")
