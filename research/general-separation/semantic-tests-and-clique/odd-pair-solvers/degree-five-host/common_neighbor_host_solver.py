"""Two-pin odd supports on degree-five hosts with the limited-common-neighbor promise."""
import argparse
from collections import Counter, deque
from itertools import combinations, product
import json
import sys

from three_connected_odd_pair import indexed_graph

WINDOW = 128


def promised(graph):
    if any(len(row) > 5 for row in graph):
        return False
    count = Counter()
    for row in graph:
        for u, v in combinations(sorted(row), 2):
            if max(len(graph[u]), len(graph[v])) == 5:
                count[u, v] += 1
                if count[u, v] >= 3:
                    return False
    return True


def odd(graph, sites, pins):
    return set(pins) <= sites and all(len(graph[v] & sites) % 2 for v in sites)


def terminal(graph, pins, degrees, seen, erased):
    p, q = pins
    start = frozenset(pins)
    level = {start}
    for size in range(2, 9):
        following = set()
        for group in level:
            if size % 2 == 0:
                local = {x: graph[x] & group for x in group}
                if erased:
                    local[p] = local[p] - {q}
                    local[q] = local[q] - {p}
                if (tuple(len(local[v]) for v in pins) == degrees
                        and all(len(r) in (1, 3, 5) for r in local.values())):
                    extra = group - start
                    if not any(odd(local, set(pins) | set(sub), pins)
                               for k in range(len(extra)) for sub in combinations(extra, k)):
                        return group
            if size < 8:
                for u in group:
                    for v in graph[u] - group - seen:
                        if not graph[v] & (seen - start):
                            following.add(group | {v})
        level = following
    return None


def steps(graph, pins, degrees, seen):
    for order in (0, 1):
        p, q = pins[order], pins[1-order]
        dp, dq = degrees[order], degrees[1-order]
        if dp != 1:
            continue
        for u in graph[p] - seen:
            if dq == 1:
                if order or graph[u] & seen != {p}:
                    continue
                for v in (graph[q] & graph[u]) - seen:
                    if graph[v] & seen == {q}:
                        for ds in product((1, 3), repeat=2):
                            yield ('P', p, q, u, v), (u, v), ds
            elif graph[u] & seen == {p, q}:
                for v in (graph[q] & graph[u]) - seen:
                    if graph[v] & seen == {q}:
                        for dv in (1, 3):
                            yield ('T', p, q, u, v), (q, v), (dq-2, dv)


def materialize(graph, pins, records, end):
    """Use occurrence numbers as abstract names so a remote physical repeat is visible."""
    images = list(pins)
    abstract = [set(), set()]
    current = (0, 1)
    caps = []
    def introduce(v):
        images.append(v)
        abstract.append(set())
        return len(images)-1
    def edge(u,v):
        abstract[u].add(v)
        abstract[v].add(u)
    for kind, a, b, x, y in records:
        p, q = current if images[current[0]] == a else current[::-1]
        assert (images[p], images[q]) == (a,b)
        u, v = introduce(x), introduce(y)
        for i,j in ((p,u),(u,v),(q,v)):
            edge(i,j)
        if kind == 'T':
            edge(u,q)
            child, gone = (q,v), (p,u)
        else:
            child, gone = (u,v), (p,q)
        caps.append((kind,p,q,u,v,gone,child))
        current = child
    active = set(current)
    # Every terminal component contains an active pin. Use an introduction
    # order with an earlier neighbor, including in the disconnected case.
    todo = set(end) - {images[i] for i in active}
    while todo:
        v = next(v for v in sorted(todo) if any(images[i] in graph[v] for i in active))
        todo.remove(v)
        i = introduce(v)
        for j in active:
            if images[j] in graph[v]:
                edge(i,j)
        active.add(i)
    if not records and pins[1] in graph[pins[0]]:
        edge(0,1)
    return abstract, images, caps


def first_conflict(graph, abstract, image):
    previous = {}
    for x, label in enumerate(image):
        if label in previous:
            raise ValueError("remote repeated name before a detectable fresh chord")
        actual = {previous[v] for v in graph[label] if v in previous}
        expected = {j for j in abstract[x] if j<x}
        if expected - actual:
            raise ValueError("missing template edge")
        if actual - expected:
            return x, actual - expected
        previous[label] = x
    return None


def repair(graph, abstract, image, caps, x, contacts):
    owners = [(i,z) for i,cap in enumerate(caps) for z in cap[5] if z in contacts]
    depth = min(i for i,z in owners)
    kind,p,q,u,v,gone,_ = caps[depth]
    earlier = {j for cap in caps[:depth] for j in cap[5]}
    erased = set(caps[depth-1][6]) if depth else set()
    def neighborhood(z):
        return abstract[z] - earlier - (erased-{z} if z in erased else set())
    pinned_leaf = p if p in contacts else q if kind=='P' and q in contacts else None
    remote = next(j for j in abstract[x] if j<x)
    X = image[x]
    if pinned_leaf is not None:
        other, parent = (q,u) if pinned_leaf==p else (p,v)
        if image[other] in graph[X]:
            keep = {pinned_leaf,other,x,remote}
            return {image[j] for j in keep | earlier}
        banned = {pinned_leaf,parent}
        size = 5
        keep = {pinned_leaf,x}
    else:
        assert kind=='T' and u in contacts
        if image[q] not in graph[X]:
            return {image[j] for j in {p,u,q,x} | earlier}
        other = q
        banned = {p,u,v}
        size = 4
        keep = {p,u,x}
    path = {other: [other]}
    queue = deque([other])
    while queue and len(path)<size:
        z = queue.popleft()
        for j in sorted(neighborhood(z) - banned - path.keys()):
            path[j] = path[z]+[j]
            queue.append(j)
            if len(path)==size:
                break
    assert len(path)==size
    end = next(j for j in path if j!=other and image[j] not in graph[X])
    keep.update(path[end])
    if sum(image[j] in graph[X] for j in keep)%2==0:
        keep.add(remote)
    return {image[j] for j in keep | earlier}


def find(lists, pins):
    graph = [set(r) for r in indexed_graph(lists)]
    if (not isinstance(pins,(list,tuple)) or len(pins)!=2 or pins[0]==pins[1]
            or any(type(v) is not int or not 0<=v<len(graph) for v in pins)):
        raise ValueError("two distinct pin indices required")
    pins = tuple(pins)
    if pins[1] in graph[pins[0]]:
        return dict(status='YES',witness=list(pins))
    if not promised(graph):
        return dict(status='UNKNOWN',witness=None)
    predecessor = {}
    queue = deque()
    for degrees in product((1,3,5), repeat=2):
        state = (pins,degrees,())
        predecessor[state] = None
        queue.append(state)
    while queue:
        state = queue.popleft()
        cur,degrees,window = state
        seen = set(cur)
        for cap in window:
            seen.update(cap[1:])
        end = terminal(graph,cur,degrees,seen,bool(window))
        if end is not None:
            records=[]
            at=state
            while predecessor[at] is not None:
                at,cap=predecessor[at]
                records.append(cap)
            abstract,image,caps=materialize(graph,pins,records[::-1],end)
            conflict=first_conflict(graph,abstract,image)
            witness=set(image) if conflict is None else repair(graph,abstract,image,caps,*conflict)
            if not odd(graph,witness,pins):
                raise AssertionError("original witness replay failed")
            return dict(status='YES',witness=sorted(witness))
        for cap,child,ds in steps(graph,cur,degrees,seen):
            nxt=(child,ds,(window+(cap,))[-WINDOW:])
            if nxt not in predecessor:
                predecessor[nxt]=(state,cap)
                queue.append(nxt)
    return dict(status='NO',witness=None)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=argparse.FileType('r'),default=sys.stdin)
    args=parser.parse_args()
    data=json.load(args.input)
    print(json.dumps(find(data['neighbors'],data['pins'])))
