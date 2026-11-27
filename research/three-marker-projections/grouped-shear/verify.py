from itertools import product
from collections import Counter, defaultdict

def dot(x,y): return (x & y).bit_count() % 2

def kernel(rows,n):
    pivots={}
    for row in rows:
        while row:
            i=row.bit_length()-1
            if i not in pivots:
                pivots[i]=row
                break
            row ^= pivots[i]
    basis=[]
    for free in set(range(n))-pivots.keys():
        x=1<<free
        for i,row in sorted(pivots.items()):
            if dot(row,x): x |= 1<<i
        basis.append(x)
    return basis

def bits(mask): return tuple(i for i in range(mask.bit_length()) if mask>>i&1)
def take(x, positions): return sum((x>>j&1)<<i for i,j in enumerate(positions))
def put(x, positions): return sum((x>>i&1)<<j for i,j in enumerate(positions))
def clause_value(c,x): return any((x>>(abs(l)-1)&1)==(l>0) for l in c)

def compute(clauses, threshold=5):
    counts=Counter(abs(l)-1 for c in clauses for l in c)
    ports=sorted(i for i in counts if counts[i]>threshold)
    where={j:i for i,j in enumerate(ports)}
    owners=defaultdict(set)
    for j,c in enumerate(clauses):
        for l in c:
            if abs(l)-1 not in where: owners[abs(l)-1].add(j)
    unseen=set(range(len(clauses)))
    tables={}
    while unseen:
        first=unseen.pop()
        comp={first}
        todo=[first]
        while todo:
            for l in clauses[todo.pop()]:
                linked=owners[abs(l)-1]&unseen
                unseen-=linked
                comp.update(linked); todo.extend(linked)
        names={abs(l)-1 for j in comp for l in clauses[j]}
        scope=tuple(sorted(names&where.keys()))
        priv=tuple(sorted(names-set(scope)))
        N=1<<len(scope)
        f=[0]*N
        for x in range(N):
            for y in range(1<<len(priv)):
                a=put(x,scope)|put(y,priv)
                if all(clause_value(clauses[j],a) for j in comp): f[x]+=1
        if scope not in tables: tables[scope]=[1]*N
        tables[scope]=[a*b for a,b in zip(tables[scope],f)]
    equations=[]
    for scope,f in tables.items():
        stab=[s for s in range(len(f)) if all(f[a]==f[a^s] for a in range(len(f)))]
        positions=[where[j] for j in scope]
        equations.extend(put(z,positions) for z in kernel(stab,len(scope)))
    return ports,tables,kernel(equations,len(ports))

def control():
    # Named ports w,p,h,a,b,t, a decorated shared literal, plus exact private copies.
    w,p,h,a,b,t=range(6)
    formulas=[((h,w,a,b),lambda H,W,A,B:H==(W^(A&B))),
              ((w,p,t),lambda W,P,T:(W^P) or T),
              ((h,p,a,b,t),lambda H,P,A,B,T:(H^P^(A&B)) or not T)]
    clauses=[]; nxt=6
    for scope, test in formulas:
        for vals in product((0,1),repeat=len(scope)):
            if test(*vals): continue
            longs=[-(i+1) if v else i+1 for i,v in zip(scope,vals)]
            while len(longs)>3:
                x,y,*rest=longs
                nxt+=1
                clauses.extend([[-x,nxt],[-y,nxt],[x,y,-nxt]])
                longs=[nxt]+rest
            clauses.append(longs)
    for i in range(6):
        for _ in range(7):
            nxt+=1
            clauses.extend([[-i-1,nxt],[i+1,-nxt]])
    ports,tables,T=compute(clauses)
    assert ports==list(range(6))
    translations={0}
    for v in T: translations|={x^v for x in translations}
    assert 7 in translations
    total=0
    for x in range(64):
        actual=1
        for scope,f in tables.items(): actual*=f[take(x,scope)]
        valid=all(test(*[(x>>j)&1 for j in scope]) for scope,test in formulas)
        assert actual==valid
        total+=actual
    print('ports',len(ports),'native clauses',len(clauses),'all 64 fiber counts verified; translation dimension',len(T),'models',total)
if __name__=='__main__': control()
