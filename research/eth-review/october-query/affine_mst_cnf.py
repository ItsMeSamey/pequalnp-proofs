"""Compile explicit signed parity bundles and residual clauses into tree coordinates."""
from dataclasses import dataclass
from signed_cover_projection import normalized,sat

def add(eq,rhs,piv):
    while eq:
        j=eq.bit_length()-1
        if j not in piv:
            piv[j]=(eq,rhs)
            return True
        a,b=piv[j]
        eq^=a
        rhs^=b
    return not rhs

def plug(eq,rhs,piv):
    for j in sorted(piv,reverse=True):
        if eq>>j&1:
            a,b=piv[j]
            eq^=a
            rhs^=b
    return eq,rhs

@dataclass(frozen=True)
class Compilation:
    n:int
    source:tuple
    clauses:tuple
    tree:tuple
    basis:tuple
    equations:tuple
    fiber:int

    def lift(self,w):
        if not 0<=w<1<<len(self.tree): raise ValueError('bad edge assignment')
        if self.fiber==0 or not all(sat(c,w) for c in self.clauses): return None
        y=0
        for j,(a,b) in enumerate(self.tree):
            if w>>j&1:
                for i in (a,b):
                    if i: y^=1<<(i-1)
        piv={}
        for a,b in self.equations: add(a,b,piv)
        for j,a in enumerate(self.basis):
            if not add(a,y>>j&1,piv): raise ArithmeticError('unattainable core')
        x=0
        for j,(a,b) in sorted(piv.items()):
            if ((a&x).bit_count()%2)^b: x|=1<<j
        if not all(sat(c,x) for c in self.source): raise ArithmeticError('wrong source witness')
        return x

def compile(n,clauses,*,scope_cap,table_cap):
    if min(n,scope_cap,table_cap)<0: raise ValueError('invalid bound')
    raw=tuple(tuple(c) for c in clauses)
    if any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('bad literal')
    rows=normalized(raw)
    unsat=Compilation(n,raw,((),),(),(),(),0)
    if frozenset() in rows: return unsat
    groups={}
    for c in rows:
        mask=sum(1<<(abs(x)-1) for x in c)
        p=sum(x<0 for x in c)%2
        groups.setdefault((mask,p),[]).append(c)
    piv={}
    equations=[]
    for (mask,p),block in groups.items():
        if len(block)==1<<(mask.bit_count()-1):
            eq=mask,1^p
            if not add(*eq,piv): return unsat
            equations.append(eq)
            rows.difference_update(block)
    basis=[]
    rep={}
    residual=[]
    for c in sorted(rows,key=lambda a:(len(a),sorted(a))):
        forms=set()
        reduced={plug(1<<(abs(x)-1),int(x<0),piv) for x in c}
        if (0,1) in reduced or any((a,b^1) in reduced for a,b in reduced): continue
        reduced.discard((0,0))
        if not reduced: return unsat
        for a,b in sorted(reduced):
            expr=0
            for j in sorted(rep,reverse=True):
                if a>>j&1:
                    v,e=rep[j]
                    a^=v
                    expr^=e
            if a:
                j=len(basis)
                basis.append(a)
                rep[a.bit_length()-1]=(a,1<<j)
                expr^=1<<j
            forms.add((expr,b))
        if (0,1) in forms or any((a,b^1) in forms for a,b in forms): continue
        forms.discard((0,0))
        if not forms: return unsat
        residual.append(tuple(sorted(forms)))
    r=len(basis)
    sig=[[sum(((a>>i)&1)<<j for j,(a,b) in enumerate(c)) for c in residual] for i in range(r)]
    sig=[[0]*len(residual)]+sig
    edges=sorted((sum(a!=b for a,b in zip(sig[i],sig[j])),i,j) for i in range(r+1) for j in range(i))
    parent=list(range(r+1))
    def find(i):
        while i!=parent[i]:
            parent[i]=parent[parent[i]]
            i=parent[i]
        return i
    tree=[]
    for _,i,j in edges:
        a,b=find(i),find(j)
        if a!=b:
            parent[a]=b
            tree.append((i,j))
    out=set()
    cost=0
    for ci,c in enumerate(residual):
        active=[j for j,(u,v) in enumerate(tree) if sig[u][ci]!=sig[v][ci]]
        if len(active)>scope_cap or (1<<len(active))>table_cap-cost: return None
        cost+=1<<len(active)
        forms=[]
        for k,(_,b) in enumerate(c):
            a=sum((((sig[tree[j][0]][ci]^sig[tree[j][1]][ci])>>k)&1)<<t for t,j in enumerate(active))
            forms.append((a,b))
        for w in range(1<<len(active)):
            if any(((a&w).bit_count()%2)^b for a,b in forms): continue
            out.add(tuple(-(j+1) if w>>t&1 else j+1 for t,j in enumerate(active)))
    return Compilation(n,raw,tuple(sorted(out)),tuple(tree),tuple(basis),tuple(equations),1<<(n-len(piv)-r))
