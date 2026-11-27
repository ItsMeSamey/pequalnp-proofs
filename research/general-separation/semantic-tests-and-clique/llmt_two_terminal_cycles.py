"""Build the unmodified reduction in LLMT §2.4 for one unsatisfiable formula."""
from itertools import product


def build():
    clauses = list(product((-1, 1), repeat=3))
    adj = {}
    def edge(a,b):
        adj.setdefault(a,set()).add(b)
        adj.setdefault(b,set()).add(a)
    def path(*nodes):
        for a,b in zip(nodes,nodes[1:]):
            edge(a,b)
    occurrences = {}
    for j,clause in enumerate(clauses):
        for i,sign in enumerate(clause):
            g = 3*j+i
            occurrences.setdefault((i,sign),[]).append(g)
            for rail in 'ab':
                for s in (-1,1):
                    path((g,rail,'in'),*((g,rail,k,s) for k in range(1,5)),(g,rail,'out'))
            for k in (1,4):
                for s in (-1,1):
                    edge((g,'a',k,s),(g,'b',k,-s))
            if g:
                for rail in 'ab':
                    edge((g-1,rail,'out'),(g,rail,'in'))
            for s,k in ((1,2),(-1,3)):
                for rail in 'ab':
                    edge((g,rail,k,-1),('c',j,i+1,s))
        for s in (-1,1):
            for k in (1,2):
                edge(('c',j,'12',s),('c',j,k,s))
            path(('c',j,'12',s),('c',j,0,s),('c',j,3,s))
        if j:
            edge(('c',j-1,0,-1),('c',j,0,1))
    for i in range(3):
        for sign in (-1,1):
            old=('d',i,1)
            for g in occurrences[i,sign]:
                l,r=('p',g,1),('p',g,2)
                edge(old,l)
                for rail in 'ab':
                    edge(l,(g,rail,2,1))
                    edge(r,(g,rail,3,1))
                old=r
            edge(old,('d',i,-1))
        if i:
            edge(('d',i-1,-1),('d',i,1))
    edge((23,'a','out'),('d',0,1))
    edge((23,'b','out'),('c',0,0,1))
    path((0,'a','in'),'x',(0,'b','in'))
    path(('d',2,-1),'y',('c',7,0,-1))
    return clauses,adj


def check():
    clauses,adj = build()
    assert not any(all(any(sign==bit for sign,bit in zip(clause,values))
                       for clause in clauses) for values in product((-1,1),repeat=3))
    first=['x',(0,'a','in'),(0,'a',1,1),(0,'b',1,-1),(0,'b','in')]
    last=['y',('d',2,-1),('p',23,2),(23,'a',3,1),(23,'a',4,1),
          (23,'b',4,-1),(23,'b',3,-1),('c',7,3,-1),('c',7,0,-1)]
    selected=set(first+last)
    assert len(selected)==14 and max(map(len,adj.values()))==3
    for cycle in (first,last):
        for i,v in enumerate(cycle):
            assert adj[v]&selected=={cycle[i-1],cycle[(i+1)%len(cycle)]}
    print(len(adj),"vertices;",sum(map(len,adj.values()))//2,"edges; induced 5- and 9-cycles")


if __name__=="__main__":
    check()
