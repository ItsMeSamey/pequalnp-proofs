"""Numerical tagged Pfaffians with canonical mask recovery, over GF(256)."""
from itertools import combinations, permutations
from random import Random
from single_cycle_check import fixture,orbits,switch

def mul(a,b):
    c=0
    while b:
        if b&1:c^=a
        a<<=1
        if a&256:a^=0x11b
        b>>=1
    return c
inv=[0]+[next(b for b in range(1,256) if mul(a,b)==1) for a in range(1,256)]
def product(values):
    acc=1
    for v in values:acc=mul(acc,v)
    return acc
def pf(M):
    m=len(M)
    if m%2:return 0
    value=1
    for i in range(0,m,2):
        j=next((j for j in range(i+1,m) if M[i][j]),None)
        if j is None:return 0
        d=i+1
        M[d],M[j]=M[j],M[d]
        for row in M:row[d],row[j]=row[j],row[d]
        p=M[i][d];value=mul(value,p)
        for a in range(d+1,m):
            for b in range(a+1,m):
                q=mul(inv[p],mul(M[i][a],M[d][b])^mul(M[i][b],M[d][a]))
                M[a][b]^=q;M[b][a]=M[a][b]
    return value

def cap(succ,marks):
    p=list(succ)
    for x,y in zip(marks,marks[1:]+marks[:1]):p[x]=succ[y]
    return p
def passive(succ,positions):
    p=list(succ);last={};out=[]
    for x in positions:
        a=last.get(x,x);b=len(p)
        p.append(p[a]);p[a]=b;last[x]=b;out.append(b)
    return p,out

class Canonical:
    def __init__(self,succ,chords):
        self.m=len(chords)//2
        ref=list(succ);self.twist=[]
        for c in chords:
            lab,_=orbits(ref)
            active=lab[c[0]]!=lab[c[1]]
            self.twist.append(int(active))
            if active:switch(ref,c)
        _,paths=orbits(ref)
        self.A=None
        if len(paths)!=1:return
        pos={v:i for i,v in enumerate(paths[0])}
        arcs=[sorted([pos[a],pos[b]]) for a,b in chords]
        self.A=[[int((a<c<b)^(a<d<b)) for c,d in arcs] for a,b in arcs]
    def at(self,weights):
        if self.A is None:return 0
        n=len(self.A);sc=[1]*n;extra=[];aug=n
        for g,(w0,w1) in enumerate(weights):
            i=2*g;j=i+1; a,b=self.twist[i:i+2];w=(w0,w1)
            if a==b:
                sc[i]=w[1-a];extra.append((i,j,w[a]))
            else:
                # aux takes i exactly if i is absent from X, i.e. when s=a
                extra.extend([(i,aug,w[a]),(j,aug,w[b])]);aug+=1
        M=[[0]*aug for _ in range(aug)]
        for i in range(n):
            for j in range(i):
                if self.A[i][j]:M[i][j]=M[j][i]=mul(sc[i],sc[j])
        for i,j,w in extra:M[i][j]^=w;M[j][i]^=w
        return pf(M)

def settings(succ,chords):
    out=[]
    for s in range(1<<(len(chords)//2)):
        p=list(succ)
        for i,c in enumerate(chords):
            if s>>(i//2)&1:switch(p,c)
        out.append(p)
    return out

def check():
    r=Random(14589); totals=[0,0,0,0]
    for trial in range(190):
        n=r.randrange(2,8);m=r.randrange(0,5) if n>=3 else 0
        gs=[r.sample(range(n),3) for _ in range(m)]
        f=r.sample(range(n),n)
        p,e,last=fixture(n,gs,f)
        k=r.randint(2,min(4,n))
        landmarks=[last+i for i in r.sample(range(n),k)]
        roots=[last+i for i in r.sample(range(n),2)]
        p,cuts=passive(p,landmarks+roots);anchors=cuts[:-2];a,b=cuts[-2:]
        states=settings(p,e)
        masks=[orbits(t) for t in states]
        protected=all(len(cs)==k and len({lab[i] for i in anchors})==k for lab,cs in masks)
        W=[(1,r.randrange(256)) for _ in gs]
        if m and trial%3==0:W[r.randrange(m)]=r.choice([(1,0),(0,1)])
        def auditcap(marks):
            capmatrix=Canonical(cap(p,marks),e)
            want=0
            for s,t in enumerate(states):
                if len(orbits(cap(t,marks))[1])==1:
                    want^=product(w[(s>>i)&1] for i,w in enumerate(W))
            assert capmatrix.at(W)==want
            return capmatrix
        rec=[auditcap([anchors[i] for i in order]) for order in permutations(range(k)) if order[0]==0]
        for s,(lab,cs) in enumerate(masks):
            exact=len(cs)==k and len({lab[i] for i in anchors})==k
            forced=[(0,1) if s>>i&1 else (1,0) for i in range(m)]
            assert exact==all(M.at(forced)==1 for M in rec)
        matrices=[auditcap([a,b])];expected2=all(len(cs)==2 for lab,cs in masks)
        if protected:
            tmp=[auditcap([a,b]+[u for u in anchors if u not in (i,j)]) for i,j in combinations(anchors,2)]
            totals[1]+=1
        def compare(mats):
            def Q(w):
                v=product(x^y for x,y in w)
                for M in mats:v^=M.at(w)
                return v
            for s,(lab,_) in enumerate(masks):
                forced=[(0,1) if s>>i&1 else (1,0) for i in range(m)]
                assert Q(forced)==int(lab[a]==lab[b])
            w=[(1,r.randrange(256)) for _ in gs]
            if Q(w)!=0:
                mask=0
                for i in range(m):
                    w[i]=(1,0)
                    if Q(w)==0:w[i]=(0,1);mask|=1<<i
                assert masks[mask][0][a]==masks[mask][0][b];totals[2]+=1
        if protected:compare(tmp)
        if expected2:compare(matrices);totals[0]+=1
        totals[3]+=len(states)
    # One optional rotation over a transposition changes which named pair meets.
    # Adjoin k-2 untouched landmark orbits, and overlap a root with a landmark.
    for k in (2,3,4,7):
        n=k+1
        f=list(range(n));f[0],f[1]=f[1],f[0]
        p,e,last=fixture(n,[(0,1,2)],f)
        labs=[orbits(t)[0] for t in settings(p,e)]
        u,v=next((u,v) for u,v in combinations(range(3),2)
                 if all(L[last+u]!=L[last+v] for L in labs))
        i,j=next((i,j) for i,j in combinations(range(3),2)
                 if (labs[0][last+i]==labs[0][last+j])!=(labs[1][last+i]==labs[1][last+j]))
        p,cuts=passive(p,[last+t for t in [u,v,*range(3,n),i,j]])
        A=cuts[:-2];a,b=cuts[-2:]
        ms=[Canonical(cap(p,[a,b]+[z for z in A if z not in (x,y)]),e) for x,y in combinations(A,2)]
        for s,t in enumerate(settings(p,e)):
            w=[(1-s,s)]; value=1
            for M in ms:value^=M.at(w)
            L=orbits(t)[0];assert value==(L[a]==L[b])
    print('nonconstant landmark examples passed at k=2,3,4,7')
    print('two-orbit fixtures, landmark fixtures, recovered witnesses, audited masks:',totals)
if __name__=='__main__':check()
