"""Exact named-kernel compression for gain-uniform vertex classes."""
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[1] / "unseeded-root-states"))
from solve import canonical, eliminate, functional


def orthogonal(rows, n):
    cols = [sum(((row >> j) & 1) << i for i,row in enumerate(rows)) for j in range(n)]
    return eliminate(cols)[1]


@dataclass(frozen=True)
class Host:
    n: int
    edges: tuple    # (first vertex, second vertex, nonnegative gain)
    classes: tuple  # class of each vertex
    roots: tuple    # low n coordinates on vertices, remaining on gain and external rows

    def validate(self):
        if self.n < 0 or len(self.classes) != self.n or any(b < 0 for b in self.roots):
            raise ValueError("inconsistent vertex or root data")
        labels = {}
        for a,b,g in self.edges:
            if not 0 <= a < b < self.n or g < 0 or (a,b) in labels:
                raise ValueError("expected simple edges with ordered endpoints")
            labels[a,b] = g
        profile = {}
        for i,j in combinations(range(self.n), 2):
            pair = tuple(sorted((self.classes[i], self.classes[j])))
            value = labels.get((i,j))
            if pair in profile and profile[pair] != value:
                raise ValueError("adjacency or gains differ within the claimed class pair")
            profile[pair] = value

    def columns(self):
        return tuple((1 << a) ^ (1 << b) ^ (g << self.n) for a,b,g in self.edges)

    def types(self):
        return [(self.classes[v], sum(((b >> v) & 1) << j for j,b in enumerate(self.roots)))
                for v in range(self.n)]


def selected(cols, mask):
    if mask < 0 or mask >> len(cols):
        raise ValueError("contracting mask out of range")
    return [v for j,v in enumerate(cols) if mask >> j & 1]


def named_kernel(host, mask):
    chosen = selected(host.columns(), mask)
    _, relations = eliminate(chosen + list(host.roots))
    return canonical(dep >> len(chosen) for dep in relations)


class Compression:
    def __init__(self, host):
        host.validate()
        self.original = host
        self.q = len(host.roots)
        self.cap = 4 << self.q
        groups = defaultdict(list)
        for v,typ in enumerate(host.types()):
            groups[typ].append(v)
        keep = []
        for vertices in groups.values():
            n = len(vertices)
            count = n if n <= self.cap else self.cap - n % 2
            keep.extend(vertices[:count])
        keep.sort()
        idx = {v:i for i,v in enumerate(keep)}
        edges = tuple((idx[a],idx[b],g) for a,b,g in host.edges if a in idx and b in idx)
        roots = tuple(((b >> host.n) << len(keep)) |
                      sum(((b >> v) & 1) << i for i,v in enumerate(keep)) for b in host.roots)
        self.small = Host(len(keep), edges, tuple(host.classes[v] for v in keep), roots)

    def transfer(self, mask, *, back):
        src,dst = (self.small,self.original) if back else (self.original,self.small)
        chosen = selected(src.columns(), mask)
        K = named_kernel(src, mask)
        phi = [functional(chosen + list(src.roots), z << len(chosen))
               for z in orthogonal(K, self.q)]
        if any(f is None for f in phi):
            raise AssertionError("named annihilator has no ambient extension")
        census = defaultdict(Counter)
        for v,typ in enumerate(src.types()):
            color = sum(((f >> v) & 1) << j for j,f in enumerate(phi))
            census[typ][color] += 1
        groups = defaultdict(list)
        for v,typ in enumerate(dst.types()):
            groups[typ].append(v)
        colors = [0] * dst.n
        for typ,vertices in groups.items():
            old = census[typ]
            counts = {c:n if n <= 2 else 4 - n%2 for c,n in old.items()}
            rest = len(vertices) - sum(counts.values())
            if rest:
                bucket = next(c for c,n in old.items() if n >= 3)
                assert rest > 0 and rest % 2 == 0
                counts[bucket] += rest
            offset = 0
            for c,n in counts.items():
                for v in vertices[offset:offset+n]:
                    colors[v] = c
                offset += n
        tails = [f >> src.n for f in phi]
        output = 0
        for i,(a,b,g) in enumerate(dst.edges):
            signature = sum(((f & g).bit_count() % 2) << j for j,f in enumerate(tails))
            if colors[a] ^ colors[b] == signature:
                output |= 1 << i
        if named_kernel(dst, output) != K:
            raise AssertionError("named kernel changed during physical transfer")
        return output

    def witness(self, target):
        target = tuple(target)
        if any(v < 0 or v >> self.q for v in target):
            raise ValueError("invalid named coefficient vector")
        target = canonical(target)
        for mask in range(1 << len(self.small.edges)):
            if named_kernel(self.small, mask) == target:
                return self.transfer(mask, back=True)
        return None
