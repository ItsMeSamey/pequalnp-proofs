"""Canonical DAG bounded synthesis with directional monotone test clauses."""
import itertools
import json
from pathlib import Path
from pysat.formula import CNF, IDPool

def cases():
    points=[2,3,4,5,6,7]
    lines=[1,3,4,5,6,7]
    flags=[(1<<i)|(1<<(6+j)) for i,p in enumerate(points)
           for j,l in enumerate(lines) if (p&l).bit_count()%2==0]
    negatives=[m for m in range(4096) if (m&63).bit_count()<=2
               and (m>>6).bit_count()<=2 and not any(m&f==f for f in flags)]
    maximal=[m for m in negatives if not any(m!=n and m&n==m for n in negatives)]
    assert len(flags)==16 and len(negatives)==120
    return [(f,True) for f in flags]+[(m,False) for m in maximal]

def encode(raws,size,tests):
    ids,cnf=IDPool(),CNF()
    def var(*key): return ids.id(key)
    first,last=raws,raws+size-1
    width=last.bit_length()
    for i in range(first,last+1):
        real,op=var('real',i),var('and',i)
        cnf.append([real] if i==first else [-real,var('real',i-1)])
        cnf.append([real,-op])
        for s in (0,1):
            picks=[var('p',i,s,j) for j in range(i)]
            cnf.append(picks)
            for a,b in itertools.combinations(picks,2): cnf.append([-a,-b])
            cnf.append([real,picks[-1]])
            for j,pick in enumerate(picks):
                for k in range(width):
                    bit=var('bit',i,s,k)
                    cnf.append([-pick,bit if j&(1<<k) else -bit])
        # Real gates have a strictly smaller left parent. Padding has two copies of i-1.
        for left in range(i):
            for right in range(left+1):
                cnf.append([-real,-var('p',i,0,left),-var('p',i,1,right)])
        for t,(mask,positive) in enumerate(tests):
            a,b=(var('arg',i,s,t) for s in (0,1))
            out=var('out',i,t)
            for s,arg in enumerate((a,b)):
                for j in range(i):
                    pick=var('p',i,s,j)
                    if j<raws:
                        raw=bool(mask&(1<<j))
                        if positive and not raw: cnf.append([-pick,-arg])
                        if not positive and raw: cnf.append([-pick,arg])
                    elif positive:
                        cnf.append([-pick,-arg,var('out',j,t)])
                    else:
                        cnf.append([-pick,-var('out',j,t),arg])
            if positive:
                cnf.extend([[-op,-out,a],[-op,-out,b],[op,-out,a,b]])
            else:
                cnf.extend([[-op,-a,-b,out],[op,-a,out],[op,-b,out]])
            if i==last: cnf.append([out if positive else -out])
    def key(i):
        return [var('and',i)]+[var('bit',i,s,k) for s in (0,1) for k in range(width)]
    for i,j in itertools.combinations(range(first,last+1),2):
        witnesses=[]
        for k,(a,b) in enumerate(zip(key(i),key(j))):
            d=var('different',i,j,k)
            cnf.extend([[-d,a,b],[-d,-a,-b]])
            witnesses.append(d)
        cnf.append(witnesses)
    for i in range(first,last):
        cnf.append([var('p',j,s,i) for j in range(i+1,last+1) for s in (0,1)])
    mapping=[dict(node=i,and_id=var('and',i),parents=[[var('p',i,s,j) for j in range(i)]
                   for s in (0,1)]) for i in range(first,last+1)]
    return cnf,mapping

if __name__=='__main__':
    directory=Path(__file__).resolve().parent
    tests=cases()
    cnf,mapping=encode(12,20,tests)
    cnf.to_file(str(directory/'input.cnf'))
    (directory/'gate-map.json').write_text(json.dumps(mapping,indent=2)+'\n')
    print(f'{len(tests)} rows; {cnf.nv} variables; {len(cnf.clauses)} clauses')
