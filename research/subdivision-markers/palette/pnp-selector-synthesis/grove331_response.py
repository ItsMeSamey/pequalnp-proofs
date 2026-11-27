"""GF(2) all-minor incidence certificate and seven-terminal response collision."""
from itertools import combinations,product

def determinant(rows):
    rows=rows.copy()
    for k in range(len(rows)):
        pivot=next((j for j in range(k,len(rows)) if rows[j]>>k&1),None)
        if pivot is None:return 0
        rows[k],rows[pivot]=rows[pivot],rows[k]
        for j in range(k+1,len(rows)):
            if rows[j]>>k&1:rows[j]^=rows[k]
    return 1

def minor(graph,I,J):
    rows=[0]*8
    for u,v in graph:
        rows[u]^=(1<<u)^(1<<v)
        rows[v]^=(1<<u)^(1<<v)
    cols=[j for j in range(8) if j not in J]
    return determinant([sum((rows[i]>>j&1)<<k for k,j in enumerate(cols)) for i in range(8) if i not in I])

def count(graph):
    target={frozenset((0,1,5)),frozenset((2,3,6)),frozenset((4,))}
    found=[]
    for F in combinations(range(len(graph)),5):
        groups=[{v} for v in range(8)]
        for i in F:
            u,v=graph[i]
            a=next(s for s in groups if u in s);b=next(s for s in groups if v in s)
            if a is b:break
            groups.remove(b);a.update(b)
        else:
            if {frozenset(s-{7}) for s in groups}==target:found.append(F)
    return found

def matrix_check():
    # Restricted growth words, all three-block partitions of the seven terminals.
    words=[p for p in product(range(3),repeat=7) if p[0]==0 and 1 in p and 2 in p and p.index(1)<p.index(2)]
    target=words.index((0,0,1,1,2,0,1))
    triples=list(combinations(range(7),3))
    trans=[sum((len({p[i] for i in t})==3)<<q for q,p in enumerate(words)) for t in triples]
    rows={}
    for a in trans:
        for b in trans:
            x=a&b
            while x and x.bit_length() in rows:x^=rows[x.bit_length()]
            if x:rows[x.bit_length()]=x
    residual=1<<target
    for k in sorted(rows,reverse=True):
        if residual>>(k-1)&1:residual^=rows[k]
    assert residual
    return len(words),len(rows),residual.bit_count()
if __name__=='__main__':
    star=[(i,7) for i in range(5)]+[(0,5),(2,6)]
    mesh=list(combinations(range(5),2))+[(4,7),(0,5),(2,6)]
    assert count(star)==[] and len(count(mesh))==1
    checked=0
    for k in range(8):
        roots=list(combinations(range(7),k))
        for i in roots:
            for j in roots:
                assert minor(star,i,j)==minor(mesh,i,j)
                checked+=1
    print(checked,count(mesh),matrix_check())
