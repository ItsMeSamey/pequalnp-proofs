"""Odd-mark tournament feasibility on a unimodal marked skeleton, with bounded deletion."""
from one_defect_uniform_tournament import components
from quadratic_target import parity


def search(rows,beta,*,deletions=0,offset=0,exact_count=False):
    n=len(rows)
    if deletions<0 or any(not 0<=v<1<<n for v in (*rows,beta,offset)):
        raise ValueError("invalid input")
    G=[r^((offset>>i&1)<<i) for i,r in enumerate(rows)]
    def edge(u,v):
        return G[v]>>u&1
    if any(edge(i,j)==edge(j,i) for i in range(n) for j in range(i)):
        raise ValueError("expected a tournament")
    def crossing(a,p,q):
        return next((a,u,v) for u in p for v in q if edge(v,u))
    def triangle(C):
        a=C[0]
        return crossing(a,[u for u in C[1:] if edge(u,a)],[u for u in C[1:] if edge(a,u)])
    def recognize(excluded,singletons):
        A=[i for i in range(n) if beta>>i&1 and i not in excluded]
        B=[i for i in range(n) if not beta>>i&1 and i not in excluded]
        ma=components(A,edge)
        for c in ma:
            if len(c)>1:
                return None,triangle(c)
        A=[c[0] for c in ma]
        blocks=components(B,edge)
        if singletons:
            for c in blocks:
                if len(c)>1:
                    return None,triangle(c)
        B=[i for c in blocks for i in c]
        boundaries={0:0}
        z=0
        for j,c in enumerate(blocks):
            z+=len(c)
            boundaries[z]=j+1
        cuts=[]
        for a in A:
            p=[i for i in B if edge(i,a)]
            if B[:len(p)]!=p or len(p) not in boundaries:
                return None,crossing(a,p,[i for i in B if edge(a,i)])
            cuts.append(boundaries[len(p)])
        peak=max(range(len(A)),key=cuts.__getitem__) if A else -1
        for i in range(1,peak+1):
            if cuts[i-1]>cuts[i]:
                return None,(A[i-1],A[i],A[peak],blocks[cuts[i]][0])
        for i in range(peak+1,len(A)):
            if cuts[i]>cuts[i-1]:
                return None,(A[peak],A[i-1],A[i],blocks[cuts[i-1]][0])
        arms=sorted([(cuts[i],0 if i<=peak else 1,i if i<=peak else -i,A[i]) for i in range(len(A))])
        stream=[]
        j=0
        for k,side,_,a in arms:
            while j<k:
                stream.append((2,blocks[j]))
                j+=1
            stream.append((side,[a]))
        stream.extend((2,c) for c in blocks[j:])
        return stream,None
    def run(stream,removed):
        total,witness=0,None
        for pattern in range(1<<len(removed)):
            fixed=sum(1<<v for j,v in enumerate(removed) if pattern>>j&1)
            tau=1^parity(fixed&beta)
            states={(0,0):(1,fixed)}
            for side,C in stream:
                nxt=dict(states)
                for (p,check),(ways,rep) in states.items():
                    left,right,B=(p>>j&1 for j in range(3))
                    ext=(left^B if side==0 else right^B^tau^1 if side==1 else left^right^B)
                    # For a nontrivial B SCC there are no deleted checks.
                    single=next((v for v in C if not(edge(v,v)^ext^parity(G[v]&fixed))),None)
                    if single is not None:
                        picked=1<<single
                    elif len(C)>1:
                        picked=sum(1<<v for v in triangle(C))
                    else:
                        continue
                    change=sum(parity(G[v]&picked)<<j for j,v in enumerate(removed) if fixed>>v&1)
                    key=p^(1<<side),check^change
                    old,oldrep=nxt.get(key,(0,rep|picked))
                    nxt[key]=old+ways,oldrep
                states=nxt
            target=sum(parity(G[v]&fixed)<<j for j,v in enumerate(removed) if fixed>>v&1)
            for (p,c),(ways,rep) in states.items():
                if parity(p&3)==tau and c==target:
                    assert parity(rep&beta) and all(not(rep>>i&1 and parity(r&rep)) for i,r in enumerate(G))
                    if not exact_count:
                        return 1,rep
                    total+=ways
                    witness=rep
        return total,witness
    stream,_=recognize(set(),exact_count)
    if stream is not None:
        ways,w=run(stream,[])
        return (ways if exact_count else ('YES' if ways else 'NO')),w
    seen=set()
    def branch(removed):
        key=tuple(sorted(removed))
        if key in seen:
            return None
        seen.add(key)
        stream,obstruction=recognize(removed,True)
        if stream is not None:
            return run(stream,key),True
        if len(removed)>=deletions:
            return None
        for v in obstruction:
            found=branch(removed|{v})
            if found is not None:
                return found
        return None
    result=branch(set()) if deletions else None
    if result is None:
        return (None if exact_count else 'UNKNOWN'),None
    (ways,w),_=result
    return (ways if exact_count else ('YES' if ways else 'NO')),w
