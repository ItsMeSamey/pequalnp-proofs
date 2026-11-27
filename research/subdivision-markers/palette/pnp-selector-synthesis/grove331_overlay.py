"""Exact char-two grove weights under supplied disk core and marked order."""
from itertools import combinations, product


def partitions(q,j):
    records=[]
    for I in combinations(range(q),j):
        for J in combinations(range(q),j):
            stack=[];blocks=[]
            for i in range(q):
                if i in I:
                    stack.append(len(blocks));blocks.append([])
                if not stack:break
                blocks[stack[-1]].append(i)
                if i in J:stack.pop()
            else:
                if not stack:records.append((sum(J)-sum(I),I,J,blocks))
    return sorted(records,reverse=True)


def laplacian(n,edges):
    L=[[0]*n for _ in range(n)]
    for u,v,w in edges:
        for a in (u,v):
            for b in (u,v):L[a][b]^=w
    return L


def evaluate(n, core, overlay, order, groups, field):
    order=tuple(order);q=len(order);where={v:i for i,v in enumerate(order)}
    if len(where)!=q or any(v<0 or v>=n for v in order):raise ValueError("invalid boundary")
    groups=tuple(tuple(g) for g in groups)
    if sorted(map(len,groups))!=[1,3,3] or len(set().union(*map(set,groups)))!=7:raise ValueError("seven distinct marks required")
    owner={where[u]:c for c,g in enumerate(groups) for u in g}
    edges=tuple((where[u],where[v],w) for u,v,w in overlay)
    L=laplacian(n,core);answer=0
    for j in range(3,q+1):
        prev=[]
        for _,I,J,blocks in partitions(q,j):
            rows=set(order[i] for i in I);cols=set(order[i] for i in J)
            weight=field.det([[L[u][v] for v in range(n) if v not in cols] for u in range(n) if u not in rows])
            for labels,z in prev:
                if len({labels[i] for i in I})==j and len({labels[i] for i in J})==j:weight^=z
            if not weight:continue
            labels={u:k for k,block in enumerate(blocks) for u in block}
            prev.append((labels,weight))
            choices=[{owner[u] for u in block if u in owner} for block in blocks]
            if any(len(c)>1 for c in choices):continue
            for assignment in product(*(c or range(3) for c in choices)):
                term=weight
                for c in range(3):
                    ids={b:i for i,b in enumerate(b for b,color in enumerate(assignment) if color==c)}
                    E=((ids[labels[u]],ids[labels[v]],w) for u,v,w in edges if labels[u] in ids and labels[v] in ids)
                    lap=laplacian(len(ids),E)
                    term=field.mul(term,field.det([row[1:] for row in lap[1:]]))
                answer^=term
    return answer
