"""Compare native socket cycles to component balance, without simplifying parallel arms."""
from collections import Counter, defaultdict, deque
from itertools import combinations_with_replacement, permutations
from random import Random


def orbit_labels(permutation):
    label = [-1] * len(permutation)
    number = 0
    for start in range(len(permutation)):
        if label[start] != -1:
            continue
        vertex = start
        while label[vertex] == -1:
            label[vertex] = number
            vertex = permutation[vertex]
        number += 1
    return label, number


def route(sigma, mask):
    return [sigma[3*(x//3) + (x%3 + ((mask >> (x//3)) & 1)) % 3]
            for x in range(len(sigma))]


def arm_gains(dual, source, target):
    parent = {source: None}
    queue = deque([source])
    while queue and target not in parent:
        face = queue.popleft()
        for neighbor, arm in dual[face]:
            if neighbor not in parent:
                parent[neighbor] = (face, arm)
                queue.append(neighbor)
    assert target in parent
    gain = set()
    while target != source:
        target, arm = parent[target]
        gain.add(arm)
    return gain


def balanced_roots(black, nblack, selected, gain, root):
    # Integer node indices distinguish disks from selected star centers.
    adjacent = defaultdict(list)
    for arm, disk in enumerate(black):
        star = arm//3
        if selected >> star & 1:
            center = nblack + star
            bit = int(arm in gain)
            adjacent[disk].append((center, bit))
            adjacent[center].append((disk, bit))
    phase = {root: 0}
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for v, bit in adjacent[u]:
            want = phase[u] ^ bit
            if v in phase:
                if phase[v] != want:
                    return set()
            else:
                phase[v] = want
                queue.append(v)
    return phase.keys()


def compare(sigma, counts):
    n = len(sigma)
    gates = n//3
    black, nblack = orbit_labels(sigma)
    white, nwhite = orbit_labels(route(sigma, (1 << gates)-1))
    if nblack + gates + nwhite - n != 2:
        return False
    # Euler characteristic two guarantees genus zero only in a connected chart.
    active = {0}
    while True:
        new = active | {sigma[x] for x in active} | {
            3*(x//3) + (x+1)%3 for x in active}
        if new == active:
            break
        active = new
    if len(active) != n:
        return False
    counts['charts'] += 1
    counts['repeated_disk_charts'] += any(
        len(set(black[pos:pos+3])) < 3 for pos in range(0,n,3))
    # Faces of incidence length two correspond to singleton white cycles.
    counts['digon_charts'] += 1 in Counter(white).values()
    dual = defaultdict(list)
    for arm in range(n):
        f, h = white[arm], white[sigma[arm]]
        dual[f].append((h, arm))
        dual[h].append((f, arm))
    gains = {(u,v): arm_gains(dual,u,v)
             for u,v in combinations_with_replacement(range(nwhite),2)}
    for mask in range(1<<gates):
        native, _ = orbit_labels(route(sigma,mask))
        cache = {}
        for a,b in combinations_with_replacement(range(n),2):
            fg = tuple(sorted((white[a],white[b])))
            key = (fg,black[a])
            if key not in cache:
                cache[key] = balanced_roots(black,nblack,mask,gains[fg],black[a])
            prediction = black[b] in cache[key]
            assert prediction == (native[a] == native[b]), (sigma,mask,a,b,fg)
            counts['mask_pairs'] += 1
            counts['joined' if prediction else 'separated'] += 1
            counts['equal_germs'] += fg[0] == fg[1]
    return True


def main():
    counts = Counter()
    for n in (3,6):
        for sigma in permutations(range(n)):
            compare(sigma,counts)
    rng = Random(46713)
    for n,limit in ((9,100),(12,60),(15,25)):
        seen = set()
        while len(seen) < limit:
            sigma = tuple(rng.sample(range(n),n))
            if sigma not in seen and compare(sigma,counts):
                seen.add(sigma)
    print(dict(sorted(counts.items())))


if __name__ == '__main__':
    main()
