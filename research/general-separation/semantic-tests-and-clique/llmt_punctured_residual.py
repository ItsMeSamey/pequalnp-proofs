"""Punctured k-space of genuine merged-guard errors on LLMT Section 2.4 graphs."""
from itertools import product


def formula(k):
    assert k>=3
    clauses=[]
    if k==3:
        clauses.append((1,2,3))
    else:
        clauses.append((1,2,3*k+1))
        for j in range(2,k-2):
            clauses.append((-(3*k+j-1),j+1,3*k+j))
        clauses.append((-(3*k+k-3),k-1,k))
    for i in range(1,k+1):
        a=k+2*i-1
        for p,q in product((1,-1),repeat=2):
            clauses.append((-i,p*a,q*(a+1)))
    return clauses


def build(clauses):
    adj={}
    def edge(a,b):
        adj.setdefault(a,set()).add(b)
        adj.setdefault(b,set()).add(a)
    occurrences={}
    for j,cl in enumerate(clauses):
        assert len({abs(v) for v in cl})==3
        for idx,lit in enumerate(cl):
            g=3*j+idx
            occurrences.setdefault(lit,[]).append(g)
            for rail in 'ab':
                for sign in (-1,1):
                    path=[(g,rail,'in')]+[(g,rail,p,sign) for p in range(1,5)]+[(g,rail,'out')]
                    for a,b in zip(path,path[1:]):
                        edge(a,b)
                if g:
                    edge((g-1,rail,'out'),(g,rail,'in'))
            for p in (1,4):
                for sign in (-1,1):
                    edge((g,'a',p,sign),(g,'b',p,-sign))
            for rail in 'ab':
                edge((g,rail,2,-1),('c',j,idx+1,1))
                edge((g,rail,3,-1),('c',j,idx+1,-1))
        for sign in (-1,1):
            for val in (1,2):
                edge(('c',j,'12',sign),('c',j,val,sign))
            edge(('c',j,'12',sign),('c',j,0,sign))
            edge(('c',j,3,sign),('c',j,0,sign))
        if j:
            edge(('c',j-1,0,-1),('c',j,0,1))
    N=max(abs(i) for cl in clauses for i in cl)
    assert all(i in occurrences and -i in occurrences for i in range(1,N+1))
    for i in range(1,N+1):
        for sign in (-1,1):
            old=('d',i,1)
            for g in occurrences[sign*i]:
                a,b=('p',g,1),('p',g,2)
                edge(old,a)
                for rail in 'ab':
                    edge(a,(g,rail,2,1))
                    edge(b,(g,rail,3,1))
                old=b
            edge(old,('d',i,-1))
        if i>1:
            edge(('d',i-1,-1),('d',i,1))
    last=3*len(clauses)-1
    edge((last,'a','out'),('d',1,1))
    edge((last,'b','out'),('c',0,0,1))
    edge('x',(0,'a','in'))
    edge('x',(0,'b','in'))
    edge('y',('d',N,-1))
    edge('y',('c',len(clauses)-1,0,-1))
    return adj


def selected(clauses,k,word):
    true={i+1 for i in range(k) if word>>i&1}
    for j in range(1,k-2):
        if not (word & ((1<<(j+1))-1)):
            true.add(3*k+j)
    def satisfied(lit):
        return (abs(lit) in true)==(lit>0)
    S={'x','y'}
    N=max(abs(i) for cl in clauses for i in cl)
    S.update(('d',i,sign) for i in range(1,N+1) for sign in (-1,1))
    for j,cl in enumerate(clauses):
        for idx,lit in enumerate(cl):
            g=3*j+idx
            sign=1 if satisfied(lit) else -1
            for rail in 'ab':
                S.update(((g,rail,'in'),(g,rail,'out')))
                S.update((g,rail,p,sign) for p in range(1,5))
            if sign==-1:
                S.update((('p',g,1),('p',g,2),(g,'a',2,1),(g,'a',3,1)))
        choice=next((i for i,l in enumerate(cl) if satisfied(l)),0)
        g=3*j+choice
        S.update(((g,'a',2,-1),(g,'a',3,-1)))
        for sign in (-1,1):
            S.update((('c',j,0,sign),('c',j,choice+1,sign)))
            if choice!=2:
                S.add(('c',j,'12',sign))
    return S


def directions(k):
    result=[]
    for i in range(k):
        clause=k-2+4*i
        g=3*clause
        result.append({(g,rail,p,-1) for rail in 'ab' for p in (2,3)}|
                      {('c',clause,1,s) for s in (-1,1)})
    return result


def certify(adj,S,want):
    par={v:len(adj[v]&S)%2 for v in S}
    assert {v for v,p in par.items() if p}==want
    visited={'x':None}
    queue=['x']
    for v in queue:
        for w in adj[v]&S:
            if w not in visited:
                visited[w]=v
                queue.append(w)
    assert len(visited)==len(S)
    # Select every internal midpoint, toggling the edges of an x-to-y path.
    M={frozenset((v,w)) for v in S for w in adj[v]&S}
    v='y'
    while visited[v] is not None:
        w=visited[v]
        M.remove(frozenset((v,w)))
        v=w
    incidence=set()
    for edge in M:
        assert edge<=S
        incidence.symmetric_difference_update(edge)
    assert incidence.symmetric_difference({'x','y'})==want


def check(k):
    clauses=formula(k)
    adj=build(clauses)
    dirs=directions(k)
    assert max(map(len,adj.values()))==3 and len(adj['x'])==len(adj['y'])==2
    assert len(set.union(*dirs))==6*k
    for w in range(1,1<<k):
        S=selected(clauses,k,w)
        certify(adj,S,set.union(*(dirs[i] for i in range(k) if w>>i&1)))
    return k,len(clauses),len(adj),sum(map(len,adj.values()))//2,(1<<k)-1


if __name__=='__main__':
    for k in (3,4,5,6):
        print("k, clauses, vertices, edges, residuals",check(k))
