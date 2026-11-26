import itertools,collections,sys,time,pickle,pathlib
import networkx as nx
from role_general import run
ns=tuple(range(7));k=len(ns);L=[{(i+d)%13 for d in (0,1,3,9)} for i in ns]; geomset=set.union(*L)
N=5**7; bn=(N+7)//8; ALL=(1<<N)-1
vals=[[-1,*sorted(A)] for A in L];T=range(7)
def setup():
 bits=[{q:bytearray(bn) for q in val} for val in vals];sb=collections.defaultdict(lambda:bytearray(bn));optlist=[]
 for i,d in enumerate(itertools.product(*vals)):
    S=tuple(t for t in T if d[t]!=-1);sb[S][i//8]|=1<<(i%8)
    optlist.append(tuple(d[t] for t in S))
    for t in T:bits[t][d[t]][i//8]|=1<<(i%8)
 return [{q:int.from_bytes(x,'little') for q,x in b.items()} for b in bits],{S:int.from_bytes(x,'little') for S,x in sb.items()},optlist
bits,sb,optlist=setup()
inc=sorted(sum(1<<t for t in T if x in L[t]) for x in range(13))
aut=[p for p in itertools.permutations(T) if sorted(sum(1<<p[t] for t in T if x in L[t]) for x in range(13))==inc]
allowed={}
for e,f,g in itertools.permutations(T,3):
 p=next(iter(L[f]&L[g]));allowed[e,f,g]=bits[f][p]|bits[g][p]|(ALL^bits[e][p] if p in L[e] else 0)
def graphs():
 candidates=[g for g in nx.graph_atlas_g() if g.number_of_edges()in range(1,8) and nx.is_connected(g)]+list(nx.nonisomorphic_trees(8))
 def rec(j,a,n,e):
    if e==7:yield nx.disjoint_union_all(a);return
    for z in range(j,len(candidates)):
        g=candidates[z];v=g.number_of_nodes();t=g.number_of_edges()
        if e+t<=7 and n+v<=10:yield from rec(z,a+[g],n+v,e+t)
 yield from rec(0,[],0,0)
def alljobs():
 for graph in graphs():
    v=graph.number_of_nodes();E=[tuple(sorted(e)) for e in graph.edges()]
    if v<5:continue
    eix={p:i for i,p in enumerate(E)}
    sym=set(tuple(eix[tuple(sorted((g[a],g[b])))] for a,b in E) for g in nx.algorithms.isomorphism.GraphMatcher(graph,graph).isomorphisms_iter())
    cap=sum((1<<i) for i in ()) # initialize zero
    for S,b in sb.items():
        r=len(S);Q=13-r-v
        if Q >= (2 if r else 3):cap|=b
    if not cap:continue
    seen=set()
    for perm in itertools.permutations(T):
        if perm in seen:continue
        variants={tuple(perm[g[i]] for i in T) for g in sym}
        for a in aut:seen.update(tuple(a[t] for t in row) for row in variants)
        G={perm[i]:p for i,p in enumerate(E)};sig=[[t for t,p in G.items() if i in p] for i in range(v)]
        mask=cap
        for e,(a,b) in G.items():
            for f in sig[a]:
                if f!=e:
                    for g in sig[b]:
                        if g!=e:mask&=allowed[e,f,g]
        if not mask:continue
        for S,b in sb.items():
            z=mask&b
            if not z:continue
            Q=13-len(S)-v;opts=[]
            while z:
                q=z&-z;i=q.bit_length()-1;z^=q
                drop=optlist[i];C=[A.copy() for A in L]
                for t,p in zip(S,drop):C[t].remove(p)
                M=[set.union(*(C[t] for t in sg)) for sg in sig]
                if any(m==geomset for m in M):continue
                possible=True
                for j,lo in enumerate(M):
                    hi=geomset.copy()
                    for t in sig[j]:
                        l,h=G[t];o=h if l==j else l;hi-=M[o]-C[t]
                    if lo==hi and (lo in L or lo in C):possible=False;break
                    R={t for t in T if len(hi&L[t])>=2}
                    if len(S)>=4 and R<=set(S) and len(R)<=4:possible=False;break
                    if len(S)>=3 and R<=set(S) and len(R)<=3:possible=False;break
                if possible:opts.append(drop)
            if opts:yield S,G,v,Q,opts
if __name__=='__main__':
 path=pathlib.Path(__file__).with_name('seven-jobs.pkl')
 if not path.exists():
    jobs=list(alljobs());path.write_bytes(pickle.dumps(jobs))
 else:jobs=pickle.loads(path.read_bytes())
 print('seven cases',len(jobs),'classes',sorted(collections.Counter((len(S),v) for S,G,v,Q,dd in jobs).items()),flush=True)
 if len(sys.argv)>1:
    start=int(sys.argv[1]);stop=int(sys.argv[2]);budget=int(sys.argv[3])
    for i in range(start,min(stop,len(jobs))):
        S,G,v,Q,dd=jobs[i];tic=time.monotonic();r,model=run(ns,S,G,v,Q,dd,budget)
        print(i,S,tuple(G.values()),v,Q,len(dd),r,round(time.monotonic()-tic,4),flush=True)
        if r:break
