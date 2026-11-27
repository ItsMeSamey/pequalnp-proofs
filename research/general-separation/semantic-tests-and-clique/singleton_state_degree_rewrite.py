"""Remove a degree-two-refuted physical state without losing three named pins."""
from itertools import combinations


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask ^= low


def quadratic_refutation(rows, pins, state=None):
    """Exact iterative degree-two PC, with an optional pair of physical constraints."""
    free = [i for i in range(len(rows)) if i not in pins]
    index = {v: 1 << i for i, v in enumerate(free)}
    terms = [0, *index.values()]
    terms.extend(index[i] | index[j] for i, j in combinations(free, 2))
    position = {m: t for t, m in enumerate(terms)}
    basis, queue = {}, []

    def insert(p):
        while p and p.bit_length() in basis:
            p ^= basis[p.bit_length()]
        if p:
            basis[p.bit_length()] = p
            if p.bit_length() <= len(free)+1:
                queue.append(p)

    for i, row in enumerate(rows):
        g = 0
        for j in bits(row):
            g ^= 1 << position[index.get(i,0) | index.get(j,0)]
        insert(g)
    if state is not None:
        v, x, y = state
        insert((1 << position[index[v]]) ^ x)
        p = y
        for j in bits(rows[v]):
            p ^= 1 << position[index.get(j,0)]
        insert(p)
    for p in queue:
        if 1 in basis:
            break
        for i in free:
            prod = 0
            for t in bits(p):
                prod ^= 1 << position[terms[t] | index[i]]
            insert(prod)
    return 1 in basis


def chart(rows, v, state, u=None):
    if state == (1,0):
        return list(rows)
    if state == (0,0):
        return [row ^ (rows[v] ^ (1<<i) if rows[v] & (1<<i) else 0)
                for i, row in enumerate(rows)]
    if state != (0,1) or u is None or not rows[v] & (1 << u):
        raise ValueError("The third chart requires an incident pivot edge.")
    endpoints = (1 << v) | (1 << u)
    new = [0]*len(rows)
    new[v] = (rows[u] & ~endpoints) | (1 << u)
    new[u] = (rows[v] & ~endpoints) | (1 << v)
    for i, row in enumerate(rows):
        if i in (u,v):
            continue
        a, b = (row>>v)&1, (row>>u)&1
        change = (rows[u] if a else 0) ^ (rows[v] if b else 0)
        new[i] = ((row ^ change) & ~endpoints) | (b << v) | (a << u)
    return new


def change_word(rows, word, v, state, u=None):
    if state == (1,0):
        return word
    y = (word & rows[v]).bit_count() % 2
    if state == (0,0):
        return word ^ ((1 ^ y) << v)
    endpoints = (1 << v) | (1 << u)
    return (word & ~endpoints) | (y << v) | (((word & rows[u]).bit_count()%2) << u)


def drop(rows, pins, v):
    lower = (1 << v)-1
    return ([(r & lower) | ((r >> (v+1)) << v) for i,r in enumerate(rows) if i!=v],
            tuple(p-int(p>v) for p in pins))


def decide(rows, pins):
    """Return YES plus original word, NO, or UNKNOWN with the remaining order."""
    stack = []
    while True:
        if quadratic_refutation(rows, pins):
            return "NO", None
        move = None
        free = set(range(len(rows))).difference(pins)
        if not free:
            word = sum(1 << p for p in pins)
            break
        for v in sorted(free):
            u = next((i for i in bits(rows[v]) if i in free),None)
            for s in ((1,0),(0,0),(0,1)):
                if s==(0,1) and u is None:
                    continue
                if quadratic_refutation(rows, pins, (v,*s)):
                    move = v,s,u
                    break
            if move:
                break
        if move is None:
            return "UNKNOWN",len(rows)
        v,s,u = move
        changed = chart(rows,v,s,u)
        stack.append((changed,v,s,u))
        rows,pins = drop(changed,pins,v)
    for changed,v,s,u in reversed(stack):
        low = (1 << v)-1
        word = (word & low) | ((word & ~low) << 1)
        word = change_word(changed,word,v,s,u)
    return "YES",word


def self_test():
    from random import Random
    from one_missing_reservoir_check import FIXTURE
    from three_pin_degree_profile import GRAPH,PINS
    from bounded_cubic_pin_pc import flat_truth
    rng = Random(817)
    counts = {}
    for rows,pins in [(FIXTURE,(0,1,2)),(GRAPH,PINS)]:
        q2 = {s:sum(quadratic_refutation(rows,pins,(v,*s))
                    for v in range(len(rows)) if v not in pins) for s in ((1,0),(0,0),(0,1))}
        print("fixture",len(rows),q2,decide(rows,pins))
    for n in range(4,11):
        for _ in range(30):
            rows = [0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    rows[i] |= 1 << j
                    rows[j] |= 1 << i
            pins = tuple(rng.sample(range(n),3))
            result,word = decide(rows,pins)
            expected = flat_truth(rows,pins)
            if result=="YES":
                assert expected and all((word>>p)&1 for p in pins)
                assert all(not(word & (1<<i)) or not((word & row).bit_count()%2)
                           for i,row in enumerate(rows))
            if result=="NO":
                assert not expected
            counts[result] = counts.get(result,0)+1
            for v in set(range(n)).difference(pins):
                u = next((i for i in bits(rows[v]) if i not in pins),None)
                if u is None:
                    continue
                s=(0,1)
                changed=chart(rows,v,s,u)
                x=rng.randrange(1<<n)
                wx=change_word(rows,x,v,s,u)
                assert chart(changed,v,s,u)==rows and change_word(changed,wx,v,s,u)==x
                assert [(x>>i&1)*((row&x).bit_count()%2) for i,row in enumerate(rows)] == [
                    (wx>>i&1)*((row&wx).bit_count()%2) for i,row in enumerate(changed)]
    print("seeded",counts)


if __name__ == "__main__":
    self_test()
