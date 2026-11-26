"""Source-only nine-flag decoder encoding. Default operation emits CNF only."""
from pathlib import Path
from itertools import combinations
import argparse, hashlib, json
from pysat.formula import IDPool,CNF
from pysat.card import CardEnc

def edges_for(g):
    if g not in (255,507,511):raise ValueError(g)
    small=[(i,j) for i,j in combinations(range(4),2) if not(g==511 and (i,j)==(2,3))]
    large=[(4+i,4+j) for j in range(5) for i in range(j) if g>>(j*(j-1)//2+i)&1]
    return small+large
def rows_for(edges):
    masks=[(1<<x)|(1<<y) for x,y in edges]
    positives={u|v for u,v in combinations(masks,2)}
    minimal=sorted(m for m in positives if not any(w!=m and (m&w)==w for w in positives))
    return [(m,False) for m in masks]+[(m,True) for m in minimal]

def encode(rows,inputs,gate_count,or_count):
    ids=IDPool(); f=CNF(); ops=[]; layers=[]
    for j in range(gate_count):
        op=ids.id(('or',j));ops.append(op)
        choice=[[ids.id(('pin',j,s,i)) for i in range(inputs+j)] for s in range(2)]
        for s,pins in enumerate(choice):
            f.extend(CardEnc.equals(pins,1,vpool=ids).clauses)
            for t,(w,_) in enumerate(rows):
                x=ids.id(('operand',j,s,t))
                for i,p in enumerate(pins):
                    if i<inputs:f.append([-p,x if w>>i&1 else -x])
                    else:
                        z=ids.id(('value',i-inputs,t));f.append([-p,z,-x]);f.append([-p,-z,x])
        for a in range(j+inputs):
            for b in range(a):f.append([-choice[0][a],-choice[1][b]])
        for t,_ in enumerate(rows):
            x,y=[ids.id(('operand',j,s,t)) for s in range(2)];z=ids.id(('value',j,t))
            f.extend([[-op,-x,z],[-op,-y,z],[-op,x,y,-z],[op,x,-z],[op,y,-z],[op,-x,-y,z]])
        layers.append(choice)
    f.extend(CardEnc.equals(ops,or_count,vpool=ids).clauses)
    for t,(_,b) in enumerate(rows):
        z=ids.id(('value',gate_count-1,t));f.append([z if b else -z])
    return f,ops,layers,ids

def evaluate(inputs,mask,gates):
    values=[bool(mask>>i&1) for i in range(inputs)]
    for op,a,b in gates:
        assert op in ('OR','AND') and 0<=a<len(values) and 0<=b<len(values)
        values.append((values[a] or values[b]) if op=='OR' else (values[a] and values[b]))
    return values[-1]

def controls(path):
    spec=json.loads(path.read_text())
    edges=edges_for(507)
    assert list(map(tuple,spec['edges']))==edges and spec['inputs']==14
    gates=spec['gates']
    assert len(gates)==39 and spec['output']==52
    # Project the first bank to its nine observed OR outputs using actual label supports.
    support=[1<<i for i in range(14)]
    for op,a,b in gates[:19]:
        assert op=='OR';support.append(support[a]|support[b])
    flags=[sum(1<<i for i,e in enumerate(edges) if v in e) for v in range(9)]
    mapping={support.index(mask):i for i,mask in enumerate(flags)}
    decoder=[]
    for j,(op,a,b) in enumerate(gates[19:]):
        decoder.append((op,mapping[a],mapping[b]))
        mapping[33+j]=9+j
    assert len(decoder)==20 and sum(op=='OR' for op,_,_ in decoder)==11
    rows=rows_for(edges)
    for mask,want in rows:assert evaluate(9,mask,decoder)==want
    for raw in range(1<<14):
        mask=sum(1<<v for v,h in enumerate(flags) if h&raw)
        assert evaluate(9,mask,decoder)==evaluate(14,raw,gates)==(raw.bit_count()>=2)
    return decoder

def check_control_cnf(cnf,ids,rows,gates):
    # Construct signal/selector values from the witness, then complete the
    # deterministic sequential counters by unit propagation, without a solver.
    val={}
    def assign(tag,b):val[ids.id(tag)]=bool(b)
    traces=[[bool(w>>j&1) for j in range(9)] for w,_ in rows]
    for j,(op,a,b) in enumerate(gates):
        a,b=sorted((a,b));assign(('or',j),op=='OR')
        for side,source in enumerate((a,b)):
            for k in range(9+j):assign(('pin',j,side,k),source==k)
        for t,v in enumerate(traces):
            x,y=v[a],v[b]
            assign(('operand',j,0,t),x);assign(('operand',j,1,t),y)
            v.append((x or y) if op=='OR' else (x and y))
            assign(('value',j,t),v[-1])
    todo=cnf.clauses
    while True:
        remaining=[];before=len(val)
        for clause in todo:
            if any(abs(l) in val and val[abs(l)]==(l>0) for l in clause):continue
            free=[l for l in clause if abs(l) not in val]
            assert free,clause
            if len(free)==1:val[abs(free[0])]=free[0]>0
            else:remaining.append(free)
        if not remaining:break
        assert len(val)>before,'counter completion undetermined'
        todo=remaining
    assert all(any(val.get(abs(l),False)==(l>0) for l in c) for c in cnf.clauses)
    print('control model checked against every CNF clause')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('graph',type=int,choices=(255,507,511))
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--control39',type=Path)
    ap.add_argument('--residual507',type=Path)
    args=ap.parse_args()
    rows=rows_for(edges_for(args.graph));n,ors=15,7
    if args.residual507:
        assert args.graph==507
        raw=json.loads(args.residual507.read_text());rg=[(op.upper(),a,b) for op,a,b in raw['gates']]
        assert len(rg)==8 and sum(op=='AND' for op,a,b in rg)==4 and raw['output']==12
        for w in range(32):assert evaluate(5,w,rg)==(w.bit_count()>=3 or w in (6,24))
    if args.control39:
        assert args.graph==507
        gates=controls(args.control39);n,ors=20,11
    cnf,ops,layers,ids=encode(rows,9,n,ors)
    if args.control39:
        # Bind the topology as well as the output rows for an encoder positive control.
        for j,(op,a,b) in enumerate(gates):
            a,b=sorted((a,b))
            cnf.extend([[ops[j] if op=='OR' else -ops[j]],[layers[j][0][a]],[layers[j][1][b]]])
        check_control_cnf(cnf,ids,rows,gates)
    cnf.to_file(args.out)
    print(args.graph,len(rows),n,ors,len(cnf.clauses),hashlib.sha256(args.out.read_bytes()).hexdigest())
if __name__=='__main__':main()
