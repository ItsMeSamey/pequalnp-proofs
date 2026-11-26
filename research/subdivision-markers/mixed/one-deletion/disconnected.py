"""Check positive/negative interpolation tables against raw disconnected bases."""
from itertools import combinations,product
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
    from check import f4,mul,div,rankf,binary

def span_table(cols,gains):
    t={0:0}
    for x,g in zip(cols,gains):
        if x in t:
            return None
        t.update({a^x:b^g for a,b in tuple(t.items())})
    return t

def scalable(columns):
    if not columns: return True
    r=len(columns[0]); s=[None]*r; t=[None]*len(columns)
    for i in range(r):
        if s[i] is not None: continue
        s[i]=1
        while True:
            old=(tuple(s),tuple(t))
            for j,col in enumerate(columns):
                for k,v in enumerate(col):
                    if not v: continue
                    if s[k] is not None:
                        a=mul(s[k],v)
                        if t[j] not in (None,a): return False
                        t[j]=a
                    if t[j] is not None:
                        b=div(t[j],v)
                        if s[k] not in (None,b): return False
                        s[k]=b
            if old==(tuple(s),tuple(t)): break
    return True

def run(parts, signals, a, gs, target):
    # Parts use separate contiguous binary coordinates. signals gives (p1_i,p2_i).
    offsets=[]; off=0
    for r,_,_ in parts:
        offsets.append(off);off+=r
    R=off
    pr1=sum(p<<o for (p,q),o in zip(signals,offsets))
    pr2=sum(q<<o for (p,q),o in zip(signals,offsets))
    clean=[v<<o for (_,V,G),o in zip(parts,offsets) for v in V]
    gains=[g for _,V,G in parts for g in G]
    qa=clean+[a]; allg=gains+[gs]
    p0=target[0]|target[1]<<2
    w=[(pr1>>i&1)|((pr2>>i&1)<<2) for i in range(R)]
    N=[[x^div(mul(y,g),p0) for x,y in zip(binary(v,R),w)] for v,g in zip(qa,allg)]
    clean_diff=False; targets=set()
    for ids in combinations(range(len(qa)),R):
        table=span_table([qa[i] for i in ids],[allg[i] for i in ids])
        if table is None: continue
        pair=(table[pr1],table[pr2]);targets.add(pair)
        fail=rankf([N[i] for i in ids])<R
        assert fail==(pair==target)
        clean_diff|= fail and len(clean) not in ids
    regular=[];root=[]
    for (r,V,G),(p,q),o in zip(parts,signals,offsets):
        z=(a>>o)&((1<<r)-1)
        full=set(); defect=set()
        for t in (r-1,r):
            for ids in combinations(range(len(V)),t):
                v=[V[i] for i in ids]; g=[G[i] for i in ids]
                if t==r:
                    B=span_table(v,g)
                    if B is not None: full.add((B[p],B[q],B[z]))
                else:
                    for gamma in range(4):
                        B=span_table(v+[z],g+[gamma])
                        if B is not None: defect.add((B[p],B[q],gamma))
        regular.append(full);root.append(defect)
    feasible=set()
    for defect in range(-1,len(parts)):
        dp={(0,0,0)}
        for i in range(len(parts)):
            table=root[i] if i==defect else regular[i]
            dp={(p^u,q^v,z^w) for p,q,z in dp for u,v,w in table}
        feasible|={(p,q) for p,q,z in dp if defect==-1 or z==gs}
    assert targets==feasible
    return scalable(N[:-1]),clean_diff, target in feasible, tuple(map(len,regular)),tuple(map(len,root))

if __name__=='__main__':
    local=(4,[1,2,4,8,7,11],[0,0,0,0,1,2])
    single=(1,[1],[0])
    # One-type / varied-gain component is scalable alone; adding an independent
    # pin in another component prevents scaling since the explicit 2x2 minor survives.
    assert run([local],[(3,0)],5,2,(1,2))[0:2]==(True,False)
    assert run([local,single],[(3,0),(0,1)],16,2,(1,2))[0:3]==(False,False,True)
    actual=(4,local[1],[0,0,0,0,1,1])
    print('genuine independent-pin disconnected case',run([actual,single],[(3,0),(0,1)],16,2,(1,2)))
    stats={}
    for target in [(1,2),(2,1),(3,2)]:
        for gs in range(4):
            for a in range(32):
                sc,dif,yes,_,_=run([actual,single],[(3,0),(0,1)],a,gs,target)
                key=(sc,dif,yes);stats[key]=stats.get(key,0)+1
    print('384 parameter cases (scalable, clean difference, feasible)',stats)
