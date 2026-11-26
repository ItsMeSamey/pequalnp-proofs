"""Relaxed five-selector receiver search on twelve resolving patterns."""
from itertools import permutations,combinations
from pysat.solvers import Minisat22
from pysat.card import CardEnc,EncType
from pathlib import Path
import sys

class Search:
    def __init__(self,pts,direct,defects,auxiliaries):
        self.cs=[];self.nv=1;self.T=1;self.cs.append([self.T]);self.pts=pts
        live=[self.row(12) for _ in range(5)]
        fs=[[live[j][i] if p>>j&1==k else -self.T for i,p in enumerate(pts)] for j in range(5) for k in (0,1)]
        # Activation at a split is a union of preceding branches or full.
        order={(j,k):self.new() for j,k in combinations(range(5),2)}
        def before(j,k):return order[j,k] if j<k else -order[k,j]
        for i,j,k in permutations(range(5),3):self.cs.append([-before(i,j),-before(j,k),before(i,k)])
        for j in range(5):
            full=self.new(); ins=[[] for _ in pts]
            for b,source in enumerate(fs):
                if b//2==j:continue
                use=self.new();self.cs.append([-use,before(b//2,j)])
                for i,v in enumerate(source):
                    if v==-self.T:continue
                    z=self.new();self.cs+=([ -z,use],[-z,v],[z,-use,-v]);ins[i].append(z)
            for i,e in enumerate(ins):
                out=live[j][i];self.cs.append([-out,full]+e);self.cs.append([-full,out])
                for z in e:self.cs.append([-z,out])
        if direct:
            # pts[0]=00000, all other points have coordinate four set.
            for i in range(1,12):self.cs.append([live[4][i]])
        for h in range(auxiliaries):
            out=self.row(12);opts=[]
            for a,b in combinations(range(len(fs)),2):
                if a<10 and b<10 and a//2==b//2:continue
                z=self.new();opts.append(z)
                for q,x,y in zip(out,fs[a],fs[b]):
                    self.cs+=([-z,-x,q],[-z,-y,q],[-z,x,y,-q])
            self.cs.append(opts);fs.append(out)
        # Equivalences of feature expressions can only relax this test.
        forms=[(a,b) for a,b in combinations(range(len(fs)),2) if not (a<10 and b<10 and a//2==b//2)]
        if direct:forms.append((9,))
        twins=[]
        for i in range(12):
            opts=[]
            for f in forms:
                if len(f)==1 and i!=0:continue
                support=[[fs[j][q] for j in f if fs[j][q]!=-self.T] for q in range(12)]
                if any(q!=i and not ls for q,ls in enumerate(support)):continue
                y=self.new();opts.append((y,set(f)))
                if len(f)==1:self.cs.append([y])
                for q,ls in enumerate(support):
                    if i==q:
                        for v in ls:self.cs.append([-y,-v])
                    else:self.cs.append([-y]+ls)
            self.cs.append([v for v,_ in opts])
            comp=[]
            for (a,f),(b,g) in combinations(opts,2):
                if f<=g or g<=f:continue
                v=self.new();self.cs+=([-v,a],[-v,b]);comp.append(v)
            if comp:
                v=self.new();self.cs.append([-v]+comp);twins.append(v)
        if len(twins)<defects:self.cs.append([])
        else:
            enc=CardEnc.atleast(twins,defects,top_id=self.nv,encoding=EncType.seqcounter)
            self.nv=max(self.nv,enc.nv);self.cs.extend(enc.clauses)
    def row(self,n):return [self.new() for _ in range(n)]
    def new(self):self.nv+=1;return self.nv

def profiles():
    perms=list(permutations(range(4)))
    maps=[[sum(((i>>k)&1)<<pi[k] for k in range(4)) for i in range(16)] for pi in perms]
    seen=set()
    for H in combinations(range(16),5):
        if H in seen:continue
        for m in maps:seen.add(tuple(sorted(m[p] for p in H)))
        yield [0]+[16+i for i in range(16) if i not in H]
if __name__=='__main__':
    direct=sys.argv[1]=='direct';d=int(sys.argv[2]);k=int(sys.argv[3]);budget=int(sys.argv[4])
    tasks=profiles() if direct else ([p for p in range(32) if C>>p&1] for C in (int(l.split()[0]) for l in Path('faceprofiles.out').read_text().splitlines()))
    count=[0,0,0]
    for ix,pts in enumerate(tasks):
        if not direct and any(len({p>>j&1 for p in pts})<2 for j in range(5)):continue
        m=Search(pts,direct,d,k)
        with Minisat22(bootstrap_with=m.cs) as sol:
            sol.conf_budget(budget);v=sol.solve_limited();count[{False:0,None:1,True:2}[v]]+=1
            print(ix,sum(1<<p for p in pts),v,sol.accum_stats()['conflicts'],flush=True)
    print('unsat unknown feasible',*count)
