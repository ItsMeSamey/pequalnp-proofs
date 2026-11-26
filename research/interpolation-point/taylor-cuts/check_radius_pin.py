"""Check six complete ordered neighborhoods in a connected exact-3 control."""
from collections import defaultdict
from graphlib import TopologicalSorter
from check_catalog_pin import Formula

def check(R):
    F=Formula(); S=(1,1,-1); fixtures=[];anchors=[]
    for test in [None]+[(i,b) for i in range(3) for b in range(2)]:
        t,b=test or (0,1); root=F.var((S[t]>0)==bool(b)); tree=[];ports={};leaves=[]
        order=defaultdict(list)
        def expand(x,p,d,forced,first):
            if d==0:
                if forced:F.forced_clause(x if F.plant[x] else -x)
                else:leaves.append((first,x))
                return
            for k in range(3):
                if k==p:continue
                good=forced and k==next(j for j in range(3) if S[j]!=S[p])
                if p is None and test:
                    good=k==(t if b else next(j for j in range(3) if S[j]!=S[t]))
                if good:assert F.plant[x]==(S[k]>0)
                values=[None]*3;values[k]=S[k]*x;sub=[]
                for j in range(3):
                    if j==k:continue
                    y=F.var((S[j]>0)!=good); values[j]=S[j]*y;sub.append((j,y))
                c=tuple(values);tree.append(c);order[x].append((k,c))
                if p is None:ports[k]=c
                for j,y in sub:
                    order[y].append((j,c))
                    expand(y,j,d-1,good,k if first is None else first)
        expand(root,None,(R+5)//2,False,None)
        dep={c:set() for c in tree}
        for entries in order.values():
            rows=[c for _,c in sorted(entries)]
            for a,v in zip(rows,rows[1:]):dep[v].add(a)
        F.clauses.extend(TopologicalSorter(dep).static_order())
        anchors.append(next(y for k,y in leaves if (k!=t if b else k==t)))
        fixtures.append((root,ports))
    for a,b in zip(anchors,anchors[1:]):F.clauses.append((a,b,F.var()))
    adj=defaultdict(list)
    for c in F.clauses:
        assert len(set(map(abs,c)))==3 and any(F.plant[abs(z)]==(z>0) for z in c)
        for j,z in enumerate(c):
            x=abs(z);label=(len(adj[x]),j,z>0)
            adj[x].append((label,c));adj[c].append((label,x))
    assert max(len(adj[x]) for x in F.plant)<=4
    def sig(x,prev,r):
        return len(adj[x]) if not r else tuple(sorted((u,sig(y,x,r-1)) for u,y in adj[x] if y!=prev))
    def edge(x,c):
        return (next(u for u,y in adj[x] if y==c),sig(x,c,R),sig(c,x,R))
    x,cs=fixtures[0]
    for i,(y,ds) in enumerate(fixtures[1:]):
        k=i//2;assert edge(x,cs[k])==edge(y,ds[k])
    seen={x};stack=[x]
    while stack:
        for _,y in adj[stack.pop()]:
            if y not in seen:seen.add(y);stack.append(y)
    assert len(seen)==len(adj)
    print(R,F.n,len(F.clauses),'six matching port balls, connected, planted, occurrence bound verified')
if __name__=='__main__':
    for R in range(1,7):check(R)
