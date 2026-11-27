"""Native planar rooted routing, with physical mask reconstruction."""
from collections import deque
from itertools import combinations

import networkx as nx

from sweep import ordered_sweep


class IncompatiblePortOrder(ValueError):
    """The physical six-port rotations have no simultaneous plane embedding."""


def _faces(perm):
    labels = [-1] * len(perm)
    for root in range(len(perm)):
        x = root
        while labels[x] < 0:
            labels[x] = root
            x = perm[x]
    return labels


def _route(sigma, bits):
    return [sigma[3*(i//3)+(i%3+bits[i//3])%3] for i in range(len(sigma))]


def _black_bits(sigma):
    wheel = nx.Graph()
    for g in range(len(sigma)//3):
        center = (g,12)
        for i in range(12):
            wheel.add_edge(center,(g,i))
            wheel.add_edge((g,i),(g,(i+1)%12))
    # Cyclic real flags out0,in0,out1,in1,out2,in2.
    for i,j in enumerate(sigma):
        wheel.add_edge((i//3,4*(i%3)),(j//3,4*(j%3)+2))
    planar, embedding = nx.check_planarity(wheel)
    if not planar:
        raise IncompatiblePortOrder("incompatible labeled wheel embedding")
    bits = []
    for g in range(len(sigma)//3):
        order = [v[1] for v in embedding.neighbors_cw_order((g,12))]
        # A uniform choice of direction around hubs chooses black globally.
        bits.append(int(order[(order.index(0)+1)%12] == 1))
    return bits


def _flood(dual,start,blocked=()):
    parent = {start:None}
    queue = deque([start])
    while queue:
        f = queue.popleft()
        for other,arm in dual[f]:
            if arm not in blocked and other not in parent:
                parent[other] = f,arm
                queue.append(other)
    return parent


def solve_native(sigma, first, second):
    """Return mask or None. Input socket x at gate g reaches sigma[3g+(x%3+bit)%3].

    first and second name incoming sockets (wire occurrences). Invalid input or
    nonplane physical rotations raise ValueError; components outside the roots
    are included in recognition and may take arbitrary switch settings.
    """
    n = len(sigma)
    if n%3 or sorted(sigma)!=list(range(n)) or any(v not in range(n) for v in (first,second)):
        raise ValueError("expected a socket permutation and two valid incoming sockets")
    black = _black_bits(sigma)
    skeleton = nx.Graph()
    skeleton.add_edges_from((i//3,j//3) for i,j in enumerate(sigma))
    component = nx.node_connected_component(skeleton,first//3)
    if second//3 not in component:
        return None
    black_step = _route(sigma,black)
    disks = _faces(black_step)
    white = _faces(_route(sigma,[1-b for b in black]))
    dual = {f:[] for f in white}
    stars = [{} for _ in black]
    for a in range(n):
        if a//3 in component:
            f,g = white[a],white[black_step[a]]
            dual[f].append((g,a))
            dual[g].append((f,a))
    src,dst = white[first],white[second]
    parents = _flood(dual,src)
    seam = set()
    f = dst
    while f!=src:
        f,arm = parents[f]
        seam.add(arm)
    representatives = {}
    for h in component:
        for a in range(3*h,3*h+3):
            d,bit = disks[a],int(a in seam)
            if d in stars[h] and stars[h][d]!=bit:
                stars[h].clear()
                break
            stars[h][d]=bit
            representatives.setdefault((h,d),a)

    def possible(allowed):
        active = [row if h in allowed else {} for h,row in enumerate(stars)]
        occupied_stars, occupied_disks = set(),set()
        cuts = []
        for h,k in combinations(sorted(allowed),2):
            if h in occupied_stars or k in occupied_stars:
                continue
            shared = active[h].keys() & active[k].keys()
            for d,e in combinations(sorted(shared-occupied_disks),2):
                if active[h][d]^active[k][d]^active[h][e]^active[k][e]:
                    arms = {representatives[z,w] for z in (h,k) for w in (d,e)}
                    inside = _flood(dual,src,arms)
                    if dst in inside:
                        raise AssertionError("odd retained cycle did not separate germs")
                    cuts.append((len(inside),((h,k),(d,e))))
                    occupied_stars.update((h,k))
                    occupied_disks.update((d,e))
                    break
        ordered = [cut for _,cut in sorted(cuts)]
        return ordered_sweep(active,disks[first],disks[second],ordered)

    allowed = {h for h in component if stars[h]}
    if not possible(allowed):
        return None
    for h in sorted(allowed):
        if possible(allowed-{h}):
            allowed.remove(h)
    bits = [b^(g in allowed) for g,b in enumerate(black)]
    labels = _faces(_route(sigma,bits))
    if labels[first]!=labels[second]:
        raise AssertionError("reconstructed physical setting does not join roots")
    return sum(b<<i for i,b in enumerate(bits))
