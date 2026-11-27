"""Cut a connected spherical simple-shadow rotation along a terminal metric tree."""
from collections import deque
from disk_patch_wedge import _check_patch


def construct(dual, rotation, tree_builder=None):
    """Return (rotation, order, access, image) for the original indexed dual."""
    n = len(dual.graph)
    rotation = [list(r) for r in rotation]
    if len(rotation) != n or len(dual.terminals) < 2:
        raise ValueError("need at least two charged vertices")
    for v, ring in enumerate(rotation):
        neighbors = {u for u, _ in dual.graph[v] if u != v}
        if set(ring) != neighbors or len(ring) != len(neighbors):
            raise ValueError("expected original simple shadow")
    darts = {(u,v) for u,ring in enumerate(rotation) for v in ring}
    faces = []
    face_at = {}
    while darts:
        start = min(darts)
        u,v = start
        face = []
        while True:
            darts.remove((u,v))
            face_at[v,u] = n+len(faces)
            face.append((v,u))
            ring = rotation[v]
            u,v = v,ring[ring.index(u)-1]
            if (u,v) == start:
                break
        faces.append(face)
    if n-sum(map(len,rotation))//2+len(faces) != 2:
        raise ValueError("expected sphere")
    radial = [[] for _ in range(n+len(faces))]
    position = {}
    for i,face in enumerate(faces,n):
        for v,source in face:
            if (v,i) not in position:
                position[v,i] = source
                radial[v].append(i)
                radial[i].append(v)
    roots = sorted(dual.terminals)
    edges = (tree_builder or metric_tree)(radial, roots)
    adj={}
    for v,w in sorted(edges):
        adj.setdefault(v,[]).append(w);adj.setdefault(w,[]).append(v)
    todo=[roots[0]]; visited=set(todo); tree=set()
    for v in todo:
        for w in adj[v]:
            if w not in visited:
                visited.add(w);todo.append(w);tree.add(tuple(sorted((v,w))))
    incident={v:set() for v in visited}
    for v,w in tree:
        incident[v].add(w);incident[w].add(v)
    image=[]; sectors=[]; copy_of={}; marks={}; tree_rot={}
    for v,ring in enumerate(rotation):
        starts={position[v,w]:w for w in incident.get(v,())}
        if not starts:
            i=len(image);image.append(v);sectors.append(list(ring))
            for u in ring:copy_of[v,u]=i
            continue
        seq=[starts[u] for u in ring if u in starts]; tree_rot[v]=seq
        for j,u in enumerate(ring):
            if u not in starts:continue
            i=len(image);image.append(v);marks[v,starts[u]]=i;part=[]
            while True:
                w=ring[j];part.append(w);copy_of[v,w]=i
                j=(j+1)%len(ring)
                if ring[j] in starts:break
            sectors.append(part)
    for f in visited:
        if f>=n:
            tree_rot[f]=[v for v,u in faces[f-n] if v in incident[f] and position[v,f]==u]
    patch=[[copy_of[u,image[i]] for u in ring] for i,ring in enumerate(sectors)]
    access={i:patch[i][0] for i in marks.values()}
    # Entering the tree vertex along w and leaving along its predecessor:
    # sector immediately AFTER the outgoing radial edge contains this mark.
    first=next(iter(tree));u,v=first;order=[]
    while True:
        ring=tree_rot[v];nxt=ring[ring.index(u)-1]
        if v<n:order.append(marks[v,nxt])
        u,v=v,nxt
        if (u,v)==first:break
    if len(order)!=len(tree):raise ValueError("incorrect radial cut boundary")
    for candidate in (order,order[::-1]):
        try:
            _check_patch(dual,patch,candidate,access,image)
        except ValueError:
            continue
        return patch,candidate,access,image
    raise ValueError("radial tree did not yield a valid disk frame")


def metric_tree(radial, roots):
    # Prim on the terminal metric. Store shortest-path parent trees for lifting.
    roots = list(roots)
    trees = {}; dist = {}
    for v in roots:
        parent = {v:None}; level = {v:0}; todo=deque([v])
        while todo:
            u=todo.popleft()
            for w in radial[u]:
                if w not in parent:
                    parent[w]=u; level[w]=level[u]+1; todo.append(w)
        trees[v]=parent; dist[v]=level
    reached={roots[0]}; edges=set()
    while len(reached)<len(roots):
        _,v,w=min((dist[v][w],v,w) for v in reached for w in roots if w not in reached)
        reached.add(w)
        while w!=v:
            u=trees[v][w]; edges.add(tuple(sorted((u,w)))); w=u
    return edges
