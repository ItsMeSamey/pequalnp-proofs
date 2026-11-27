"""Gate-level replay, including cubic degree-drop preprocessing."""
from itertools import combinations
from pathlib import Path
from runpy import run_path
from random import Random

base = run_path(str(Path(__file__).with_name('check-quadratic.py')))
gauss = base['gauss']
compressed = base['compressed']
brute = base['brute']

def normalize(n, circuit, pins=None):
    pins = pins or {}
    wires = [pins.get(i, 1 << (i+1)) for i in range(n)]
    products = []
    for table, i, j in circuit:
        a,b = wires[i], wires[j]
        zero, left, right, both = [(table >> h) & 1 for h in range(4)]
        value = zero ^ (a if left ^ zero else 0) ^ (b if right ^ zero else 0)
        if zero ^ left ^ right ^ both:
            value ^= 1 << (1+n+len(products))
            products.append((a,b))
        wires.append(value)
    return products, wires[-1]

def replay(n, circuit):
    def count(pins):
        gates,out = normalize(n,circuit,pins)
        return compressed(n,gates,out) >> len(pins)
    full = count({})
    if not full:
        return 0,None
    pins = {}
    for i in range(n):
        pins[i] = 0
        if not count(pins):
            pins[i] = 1
    return full,sum(v << i for i,v in pins.items())

def vanish_form(n, poly):
    top = {m for m in poly if m.bit_count() == 3}
    rows = {}
    for col in combinations(range(n),4):
        quad = sum(1 << i for i in col)
        row = sum(1 << i for i in col if quad ^ (1 << i) in top)
        for pivot in sorted(rows,reverse=True):
            if row >> pivot & 1:
                row ^= rows[pivot]
        if row:
            rows[row.bit_length()-1] = row
    free = next((i for i in range(n) if i not in rows),None)
    if free is None:
        return 0
    v = 1 << free
    for i in sorted(rows):
        if (rows[i] & v).bit_count() & 1:
            v ^= 1 << i
    return v

def slice_sum(n, poly):
    if not any(m.bit_count()==3 for m in poly):
        return gauss(poly,n)
    form = vanish_form(n,poly)
    if not form:
        return None
    pivot = form & -form
    support = [1 << i for i in range(n) if (1 << i) & (form ^ pivot)]
    total = 0
    for value in (0,1):
        q = set()
        for m in poly:
            if not m & pivot:
                q ^= {m}
                continue
            rest = m ^ pivot
            if value:
                q ^= {rest}
            for t in support:
                q ^= {rest | t}
        assert all(m.bit_count()<=2 for m in q)
        total += gauss(q,n)//2   # dummy former pivot
    return total

if __name__ == '__main__':
    rng = Random(20261128)
    for case in range(100):
        n = rng.randrange(1,6)
        circuit = [(rng.randrange(16),rng.randrange(n+i),rng.randrange(n+i))
                   for i in range(rng.randrange(1,7))]
        gates,out = normalize(n,circuit)
        found,witness = replay(n,circuit)
        good = []
        for x in range(1 << n):
            bits = [(x>>i)&1 for i in range(n)]
            for table,i,j in circuit:
                bits.append((table >> (bits[i]+2*bits[j]))&1)
            if bits[-1]:
                good.append(x)
        assert found == len(good) and (witness in good if good else witness is None)
    count = 0
    for n in range(1,8):
        for _ in range(40):
            poly = {m for m in range(1 << n) if m.bit_count()<=3 and rng.randrange(2)}
            ans = slice_sum(n,poly)
            if ans is not None:
                expected = sum((-1)**sum(x&m==m for m in poly) for x in range(1<<n))
                assert ans == expected
                count += 1
    n=14
    common_factor = {1 | (1<<i) | (1<<j) for i,j in combinations(range(1,n),2)}
    assert slice_sum(n,common_factor) == sum((-1)**sum(x&m==m for m in common_factor) for x in range(1<<n))
    print('100 gate-level count/witness checks;',count,'random verified slice sums; 78-cubic shared-factor example passed')
