"""Four-cap search for induced all-odd supports through two named vertices."""
import argparse
from collections import deque
from itertools import combinations, product
import json
import sys

from three_connected_odd_pair import indexed_graph
from common_neighbor_host_solver import first_conflict, odd

WINDOW = 1024


def pair(i, j):
    return (min(i, j), max(i, j))


def neighbors(graph, flips, v):
    row = graph[v].copy()
    for a, b in flips:
        if v == a:
            row.symmetric_difference_update((b,))
        elif v == b:
            row.symmetric_difference_update((a,))
    return row


def odd_options(full, required, maximum):
    if not required <= full:
        return
    extras = sorted(full - required)
    for k in range(1, maximum + 1, 2):
        if 0 <= k - len(required) <= len(extras):
            for choice in combinations(extras, k-len(required)):
                yield required | set(choice)


def boundaries(graph, pins, mandatory, flips, blocked, forbidden, high=False):
    """Expose complete selected rows of both new pins. Forbid fresh old-pin contacts."""
    p, q = pins
    rows = [neighbors(graph, flips, i) for i in pins]
    options = []
    for row in rows:
        allowed = {v for v in row-blocked
                   if v in mandatory or not graph[v] & forbidden}
        options.append(odd_options(allowed, row & mandatory, 7 if high else 5))
    for left, right in product(*options):
        B = mandatory | left | right
        if left == B & rows[0] and right == B & rows[1] and B == set(pins) | left | right:
            yield tuple(sorted(B))


def terminals(graph, state):
    pins, B, flips, window = state
    p, q = pins
    base = frozenset(B)
    rows = {v: neighbors(graph, flips, v) for v in B}
    deg = [len(rows[v] & base) for v in pins]
    exceptional = max(deg) == 7
    if exceptional:
        small, big = sorted(pins, key=lambda v: len(rows[v] & base))
        if (not window or window[-1][0] not in ('N','A') or sorted(deg) != [3,7]
                or not (rows[small] & base) <= (rows[big] & base)):
            return
    bound = 10 if exceptional else 8
    blocked = {v for cap in window for v in removed(cap)}
    seen = {base}
    for size in range(len(base), bound+1):
        more = set()
        for selected in seen:
            if size % 2 == 0 and (not exceptional or size == 10):
                local = {v: neighbors(graph, flips, v) & selected for v in selected}
                if all(len(r) in ((1,3,5,7) if v in pins else (1,3,5))
                       for v,r in local.items()):
                    extra = sorted(selected-set(pins))
                    if not any(odd(local,set(pins)|set(sub),pins)
                               for k in range(len(extra)) for sub in combinations(extra,k)):
                        yield selected
            if size == bound:
                continue
            for u in selected:
                for v in graph[u]-selected-blocked:
                    if not graph[v] & (blocked | set(pins)):
                        more.add(selected | {v})
        seen=more


def removed(cap):
    kind,p,q,u,v,C,B,D=cap
    return (p,q) if kind=='P' else (p,u)


def flip_edges(kind,q,u,v,C):
    if kind=='P':
        return {pair(u,v)}
    changed = {pair(q,v)} if kind in ('T','A') else set()
    if kind in ('N','A'):
        changed.update(pair(v,c) for c in C)
    return changed


def moves(graph, state):
    pins,B0,flips,window = state
    B=set(B0)
    prior={v for cap in window for v in removed(cap)}
    for p,q in (pins,pins[::-1]):
        rp=neighbors(graph,flips,p)&B
        rq=neighbors(graph,flips,q)&B
        if len(rp)!=1 or len(rq)>5 or q in rp:
            continue
        u,=rp
        raw=neighbors(graph,flips,u)
        candidates=[]
        if len(rq)==1:
            if p!=pins[0]:continue
            v,=rq
            if v!=u and v in raw:
                candidates.append(('P',v,set()))
        elif q in raw:
            C=raw & rq
            E=rq-{u}-C
            if raw&B == {p,q}|C:
                if len(C)==1 and len(E) in (1,3):
                    candidates.append(('T',next(iter(C)),set()))
                elif len(C)==3 and len(E)==1:
                    candidates.append(('A',next(iter(E)),C))
        elif len(rq)==3 and rq<=raw:
            for v in raw - rq - {p,q} - prior:
                if v not in B and graph[v] & (prior | set(pins)):continue
                if raw&B <= {p,v}|rq:
                    candidates.append(('N',v,rq))
        for kind,v,C in candidates:
            gone={p,q} if kind=='P' else {p,u}
            remaining=(B|{v})-gone
            child=(u,v) if kind=='P' else (q,v)
            edits=flip_edges(kind,q,u,v,C)
            changes={edge for edge in set(flips)^edits if not gone.intersection(edge)}
            # All other new sites are physically nonadjacent to the two now
            # closed original pin rows and the removed site(s).
            forbid=prior|gone|set(pins)
            for D in boundaries(graph,child,remaining,changes,prior|gone,forbid,kind in ('N','A')):
                if len(window)>=24 and set(D).intersection(*(set(cap[6]) for cap in window[-24:])):
                    continue
                # All intended adjacencies from a closed nonpin parent are now known.
                total=B|set(D)
                if kind=='T' and raw&total!={p,q,v}:continue
                if kind=='N' and raw&total!={p,v}|C:continue
                if kind=='A' and raw&total!={p,q}|C:continue
                cap=kind,p,q,u,v,tuple(sorted(C)),B0,D
                yield (child,D,tuple(sorted(changes)),(window+(cap,))[-WINDOW:]),cap


def solve_search(graph, pins):
    roots=boundaries(graph,pins,set(pins),set(),set(),set())
    queue=deque()
    prev={}
    for B in roots:
        state=(pins,B,(),())
        prev[state]=None
        queue.append(state)
    while queue:
        state=queue.popleft()
        for end in terminals(graph,state):
            path=[]
            at=state
            while prev[at] is not None:
                at,cap=prev[at]
                path.append(cap)
            result=recover(graph,pins,at[1],path[::-1],end)
            if not odd(graph,result,pins):
                raise AssertionError("failed original incidence replay")
            return sorted(result)
        for nxt,cap in moves(graph,state):
            if nxt not in prev:
                prev[nxt]=state,cap
                queue.append(nxt)
    return None


def trace_graph(graph,pins,initial,path,end):
    """Give each introduction a distinct occurrence ID and record its intended edges."""
    images=list(pins)
    active={v:i for i,v in enumerate(pins)}
    adj=[set(),set()]
    layout=[]
    def expose(names,mandatory_first=None):
        pool=set(names)-active.keys()
        while pool:
            if mandatory_first in pool:
                label=mandatory_first
                mandatory_first=None
            else:
                label=next(v for v in sorted(pool) if graph[v] & active.keys())
            index=len(images)
            adj.append(set())
            images.append(label)
            for other in graph[label]&active.keys():
                j=active[other]
                adj[j].add(index)
                adj[index].add(j)
            active[label]=index
            pool.remove(label)
    expose(initial)
    for kind,p,q,u,v,C,B,D in path:
        expose(D,v if kind=='N' else None)
        cap=(kind,active[p],active[q],active[u],active[v],tuple(active[c] for c in C))
        layout.append(cap)
        for gone in ((p,q) if kind=='P' else (p,u)):
            del active[gone]
    expose(end)
    return adj,images,layout


def recover(graph,pins,initial,path,end):
    abstract,image,layout=trace_graph(graph,pins,initial,path,end)
    conflict=first_conflict(graph,abstract,image)
    if conflict is None:
        return set(image)
    x,contacts=conflict
    return repair_trace(graph,abstract,image,layout,x,contacts)


def repair_trace(graph,abstract,image,layout,x,contacts):
    earlier=set()
    for kind,p,q,u,v,C in layout:
        gone={p,q} if kind=='P' else {p,u}
        if contacts&gone or (kind in ('A','N') and q in contacts):
            break
        for a,b in flip_edges(kind,q,u,v,C):
            abstract[a].symmetric_difference_update({b})
            abstract[b].symmetric_difference_update({a})
        earlier |= gone
    else:
        raise AssertionError("remote chord without a sensitive cap")
    X=image[x]
    U=next(j for j in abstract[x] if j<x)
    leaf=p if p in contacts else q if kind=='P' and q in contacts else None
    if leaf is not None:
        other,parent=(q,u) if leaf==p else (p,v)
        if image[other] in graph[X]:
            kept={leaf,other,x,U}
        else:
            kept={leaf,x}
            avoid={leaf,parent}
            need=5
    elif kind in ('A','N'):
        if kind!='N' or q not in contacts or u in contacts:
            raise AssertionError("saturated cap has an extra incidence")
        kept={p,u,q,x}
    elif image[q] not in graph[X]:
        kept={p,u,q,x}
    else:
        kept={p,u,x}
        other=q
        avoid={p,u,v}
        need=4
    if len(kept)<4:
        paths={other:[other]}
        queue=deque([other])
        while queue and len(paths)<need:
            z=queue.popleft()
            for j in sorted(abstract[z]-earlier-avoid-paths.keys()):
                paths[j]=paths[z]+[j]
                queue.append(j)
                if len(paths)==need:break
        end=next(j for j in paths if j!=other and image[j] not in graph[X])
        kept.update(paths[end])
        if sum(image[j] in graph[X] for j in kept)%2==0:
            kept.add(U)
    return {image[j] for j in earlier|kept}


def find(lists,pins):
    graph=[set(row) for row in indexed_graph(lists)]
    if (not isinstance(pins,(tuple,list)) or len(pins)!=2 or pins[0]==pins[1]
            or any(type(v) is not int or not 0<=v<len(graph) for v in pins)):
        raise ValueError("two distinct vertex indices required")
    p,q=pins
    if q in graph[p]:
        return dict(status='YES',witness=[p,q])
    if any(len(row)>5 for row in graph):
        return dict(status='UNKNOWN',witness=None)
    witness=solve_search(graph,(p,q))
    return dict(status='YES' if witness is not None else 'NO',witness=witness)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=argparse.FileType('r'),default=sys.stdin)
    args=parser.parse_args()
    data=json.load(args.input)
    print(json.dumps(find(data['neighbors'],data['pins'])))
