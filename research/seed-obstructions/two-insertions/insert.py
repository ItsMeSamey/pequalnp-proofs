"""Allow two arbitrary inserted AND/OR gates, independent rerouting of every seed input port, and either new output."""
from pathlib import Path
import argparse, json, random, time
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.examples.hitman import Hitman
root=Path(__file__).parent
rows=list(map(int,(root/'data.txt').read_text().split()))
seed=[tuple(map(int,l.split())) for l in (root/'absorbed31.txt').read_text().splitlines()]
assert len(rows)==273 and len(seed)==31
class Enc:
    def __init__(self,solver='cadical195',rewires=0,unordered=False):
        self.pool=IDPool();self.s=Solver(name=solver)
        new=self.pool.id;add=self.s.add_clause
        self.unordered=unordered
        self.cut=[[new() for _ in seed] for _ in range(2)]
        for c in self.cut:
            for a,b in zip(c,c[1:]):add([-a,b])
        for a,b in zip(*self.cut):add([-b,a])
        def choices(count):
            v=[new() for _ in range(count)];add(v)
            for clause in CardEnc.atmost(v,1,vpool=self.pool,encoding=EncType.seqcounter).clauses:add(clause)
            return v
        self.ops=[new(),new()];self.source=[];self.route=[];self.changes=[]
        for n in range(2):
            a=choices(69+n);b=choices(69+n)
            for j,x in enumerate(a):add([-x]+b[j:])
            for port in (a,b):
                if not unordered:
                    for i in range(31):add([-port[38+i],-self.cut[n][i]])
            self.source.append((a,b))
        self.alt=[];self.rewired=[]
        for i,(_,a,b) in enumerate(seed):
            rr=[choices(3+bool(rewires)),choices(3+bool(rewires))]
            aa=[]
            if rewires:
                for r,old in zip(rr,(a,b)):
                    self.rewired.append(r[3]);v=choices(38+i);add([-v[old]]);aa.append(v)
            self.alt.append(aa)
            for r in rr:
                if not unordered:
                    add([-r[1],self.cut[0][i]]);add([-r[2],self.cut[1][i]])
                self.changes.append(-r[0])
            self.route.append(rr)
        if rewires:
            for c in CardEnc.atmost(self.rewired,rewires,vpool=self.pool,encoding=EncType.seqcounter).clauses:add(c)
        if unordered:
            for j in range(2):
                affected=[new() for _ in seed]
                for i,(_,a,b) in enumerate(seed):
                    for k,old in enumerate((a,b)):
                        r=self.route[i][k];add([-r[j+1],affected[i]])
                        if old>=38:add([-r[0],-affected[old-38],affected[i]])
                        if self.alt[i]:
                            for v,x in enumerate(self.alt[i][k][38:]):
                                add([-r[3],-x,-affected[v],affected[i]])
                for n in range(j+1):
                    for port in self.source[n]:
                        for i,v in enumerate(affected):add([-port[38+i],-v])
        self.output=choices(3)
        self.used_rows=set()
    def budget(self,k):
        if k<62:
            for c in CardEnc.atmost(self.changes,k,vpool=self.pool,encoding=EncType.seqcounter).clauses:self.s.add_clause(c)
    def add_row(self,idx,target=None):
        if idx in self.used_rows:return
        self.used_rows.add(idx);r=rows[idx];new=self.pool.id;add=self.s.add_clause
        w=[bool(r>>j&1) for j in range(38)]+[new() for _ in range(33)]
        def neg(x):return not x if type(x) is bool else -x
        def clause(c):
            if not any(x is True for x in c):add([x for x in c if x is not False])
        def mux(sel,vals):
            z=new()
            for s,x in zip(sel,vals):
                clause([-s,-z,x]);clause([-s,z,neg(x)])
            return z
        def opgate(z,x,y,op):
            pre=[] if op is True else [-op] if type(op) is not bool else None
            if pre is not None:
                for c in [[-z,x],[-z,y],[z,neg(x),neg(y)]]:clause(pre+c)
            pre=[] if op is False else [op] if type(op) is not bool else None
            if pre is not None:
                for c in [[z,neg(x)],[z,neg(y)],[-z,x,y]]:clause(pre+c)
        for i,(op,a,b) in enumerate(seed):
            vals=[[w[a],w[69],w[70]],[w[b],w[69],w[70]]]
            for k,alt in enumerate(self.alt[i]):vals[k].append(mux(alt,w[:38+i]))
            x=mux(self.route[i][0],vals[0]);y=mux(self.route[i][1],vals[1])
            opgate(w[38+i],x,y,bool(op))
        for j,(a,b) in enumerate(self.source):
            opgate(w[69+j],mux(a,w[:69+j]),mux(b,w[:69+j]),self.ops[j])
        if target is None:target=idx<28
        for sel,z in zip(self.output,w[68:71]):add([-sel,z if target else -z])
    def model(self):
        m=set(self.s.get_model());pick=lambda v:next(i for i,x in enumerate(v) if x in m)
        cuts=[sum(v not in m for v in c) for c in self.cut]
        order=[]
        for i in range(32):
            for j,k in enumerate(cuts):
                if i==k:order.append(69+j)
            if i<31:order.append(38+i)
        raw={}
        for i,(op,a,b) in enumerate(seed):
            rr=[pick(v) for v in self.route[i]]
            vals=[[a,69,70],[b,69,70]]
            for k,alt in enumerate(self.alt[i]):vals[k].append(pick(alt))
            raw[38+i]=(op,vals[0][rr[0]],vals[1][rr[1]])
        for j,(a,b) in enumerate(self.source):
            raw[69+j]=(int(self.ops[j] in m),pick(a),pick(b))
        out=[68,69,70][pick(self.output)]
        if self.unordered:
            order=[];todo=set(raw);known=set(range(38))
            while todo:
                ready=sorted(k for k in todo if raw[k][1] in known and raw[k][2] in known)
                assert ready
                for k in ready:order.append(k);known.add(k);todo.remove(k)
        used={out}
        for v in reversed(order):
            if v in used:used.update(raw[v][1:])
        idx={i:i for i in range(38)};net=[]
        for v in order:
            if v in used:
                op,a,b=raw[v];assert a in idx and b in idx
                idx[v]=38+len(net);net.append((op,idx[a],idx[b]))
        return net,cuts
def test(net):
    w=[sum(((r>>j)&1)<<i for i,r in enumerate(rows)) for j in range(38)]
    for op,a,b in net:w.append(w[a]&w[b] if op else w[a]|w[b])
    diff=w[-1]^((1<<28)-1)
    return [i for i in range(273) if diff>>i&1]
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--routes',type=int,default=62);parser.add_argument('--budget',type=int,default=30000)
    parser.add_argument('--steps',type=int,default=100);parser.add_argument('--seed',type=int,default=151)
    parser.add_argument('--solver',default='cadical195');parser.add_argument('--rewires',type=int,default=0);parser.add_argument('--unordered',action='store_true')
    args=parser.parse_args();rng=random.Random(args.seed);enc=Enc(args.solver,args.rewires,args.unordered);enc.budget(args.routes)
    initial=set(test(seed)+rng.sample(range(28),8)+rng.sample(range(28,273),12))
    for i in initial:enc.add_row(i)
    best=274
    for step in range(args.steps):
        enc.s.conf_budget(args.budget);st=enc.s.solve_limited()
        if st is not True:print(step,'rows',len(enc.used_rows),'UNSAT' if st is False else 'UNKNOWN',flush=True);break
        net,cuts=enc.model();bad=test(net);assert not set(bad)&enc.used_rows
        print(step,'rows',len(enc.used_rows),'errors',len(bad),'cuts',cuts,'live',len(net),flush=True)
        if len(bad)<best:
            best=len(bad);(root/f'best-{args.rewires}-{args.solver}-{args.seed}-{int(args.unordered)}.json').write_text(json.dumps(dict(bad=bad,gates=net)))
        if not bad:(root/f'witness-{args.routes}.json').write_text(json.dumps(net));break
        for i in rng.sample(bad,min(5,len(bad))):enc.add_row(i)
