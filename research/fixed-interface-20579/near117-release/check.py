from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json,re,runpy,sys
HERE=Path(__file__).resolve().parent
def check(b,msg):
    if not b:raise ValueError(msg)
def frozen():
    s=(HERE/'control.lean').read_bytes();t=(HERE/'statement.txt').read_bytes()
    check(sha256(s).hexdigest()=='08b07ebb1edfb826bb061afcc09558ae5d75a6d4d626e43c373c4d8e6855d731','control digest')
    check(sha256(t).hexdigest()=='e233b9b26bab1a8856b41abefce91ad2660f5139effd3df1ad8e11582240f816','statement digest')
    G={i:tuple(map(int,g)) for i,g in enumerate(re.findall(rb'\((\d+),(\d+),(\d+)\)',s),64)}
    v={i:sum(1<<(32*r+c) for r in range(32) for c in range(32) if i==r or i==32+c) for i in range(64)}
    for w,(o,a,b) in G.items():v[w]=v[a]|v[b] if o else v[a]&v[b]
    target=sum(int(h,16)<<(32*r) for r,h in enumerate(re.findall(rb'0x([0-9a-f]+)',t)))
    check(len(G)==180 and v[243]==target,'control output')
    v[244]=((1<<1024)-1)^v[121]
    check(sum((v[244]>>(33*i)&1)<<i for i in range(6))==53,'shard')
    roots={220,223,224,225,226};stack=[243,121];kept=set()
    while stack:
        w=stack.pop()
        if w<64 or w in roots or w in kept:continue
        kept.add(w);stack.extend(G[w][1:])
    region=set(G)-kept
    old=sorted({j for w in region for j in G[w][1:]}-region);paid=sorted(set(range(64))|{w for w in kept if w<213})
    leaves=[];stack=[243]
    while stack:
        w=stack.pop()
        if 213<=w<=228:leaves.append(w);continue
        check(w>=229 and G[w][0]==1,'OR suffix');stack.extend(G[w][1:])
    check(sorted(leaves)==list(range(213,229)) and all(G[w][0]==0 for w in leaves),'terminal list')
    other=0
    for w in set(leaves)-roots:other|=v[w]
    P=[i for i in range(1024) if (target&~other)>>i&1];N=[i for i in range(1024) if not(target>>i&1)]
    check((len(kept),len(old),len(paid),len(P),len(N))==(140,39,178,98,613),'splice counts')
    return v,old,paid,P,N,region
def analyze(B,allsig,pos,neg):
    B=sorted(B);bits={w:1<<w for w in B};mask=sum(bits.values())
    P={allsig[i]&mask:i for i in pos};N={allsig[i]&mask:i for i in neg}
    check(P.keys().isdisjoint(N),'inseparable bank')
    needed={}
    for w,k in bits.items():
        pair=next(([i,N[p^k]] for p,i in P.items() if p^k in N),None)
        if pair:needed[w]=pair
    opts=sorted(set(B)-needed.keys());base=sum(bits[w] for w in needed)
    for size in range(len(opts)+1):
        feasible=[]
        for add in combinations(opts,size):
            use=base|sum(bits[w] for w in add)
            if {p&use for p in P}.isdisjoint({n&use for n in N}):feasible.append(list(add))
        if feasible:break
    minimum=len(needed)+size
    descent=next(([i,j] for p,i in P.items() for n,j in N.items() if p&n==p),None)
    wedges={}
    for centers,other in [(P,N),(N,P)]:
        for p,i in centers.items():
            ns=[w for w,k in bits.items() if p^k in other]
            for a,b in combinations(ns,2):
                loc=2*bool(p&bits[a])+bool(p&bits[b])
                wedges.setdefault((a,b),{})[loc]=[i,other[p^bits[a]],other[p^bits[b]]]
    adj={w:set() for w in B}
    for (a,b),loc in wedges.items():
        if len(loc)>1:adj[a].add(b);adj[b].add(a)
    best=[]
    def grow(candidates,clique):
        nonlocal best
        if len(clique)>len(best):best=sorted(clique)
        while len(candidates)+len(clique)>len(best):
            w=min(candidates);candidates.remove(w);grow(candidates&adj[w],clique+[w])
    grow(set(B),[])
    edges=[]
    for a,b in combinations(best,2):
        ws=wedges[a,b];edges.append([a,b,*[ws[q] for q in sorted(ws)[:2]]])
    lower=minimum+int(descent is not None)+max(0,len(best)-1)-5
    return dict(bank=B,essential=[[w,*pair] for w,pair in sorted(needed.items())],
                optional=opts,minimum_additions=feasible,min_inputs=minimum,
                descent=descent,clique=best,wedges=edges,lower=lower)

def main():
    v,old,paid,P,N,D=frozen()
    banks,provenance=runpy.run_path(str(HERE/'family.py'))['generate_banks'](old,paid,v,P,N)
    allsig={i:sum((v[w]>>i&1)<<w for w in paid+[244]) for i in P+N}
    result=[];first=Counter();final=Counter()
    for B in banks:
        r=analyze(list(B)+[244],allsig,P,N);first[r['lower']]+=1
        final_lb=r['lower']
        if r['lower']==29:
            used=[a[0] for a in r['essential']]
            projections=[analyze(used+opts,allsig,P,N) for opts in r['minimum_additions']]
            r['minimum_projections']=projections
            final_lb=min(r['lower']+1,min(p['lower'] for p in projections))
        r['final_lower']=final_lb;final[final_lb]+=1;result.append(r)
    check(len(banks)==117 and first=={29:1,30:36,31:32,32:48},'family aggregate lower bounds')
    check(final=={30:37,31:32,32:48},'refined lower bounds')
    cert=dict(roots=[220,223,224,225,226],region=sorted(D),original=old,paid=paid,
              provenance=provenance,banks=result)
    # Stable JSON normalization also converts tuple-valued provenance to lists.
    encoded=json.dumps(cert,sort_keys=True,separators=(',',':'))+'\n'
    if sys.argv[1:]==['--write-certificates']:
        (HERE/'certificates.json').write_text(encoded)
    else:
        check(not sys.argv[1:] and (HERE/'certificates.json').read_text()==encoded,'frozen certificate mismatch')
    print('Verified 117 fixed banks; local lower bounds 30 gates for 37, 31 for 32, 32 for 48.')
    print('All exceed the 29 gates available with 141 retained gates and five ports.')
if __name__=='__main__':main()
