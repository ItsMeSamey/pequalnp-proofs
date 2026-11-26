from itertools import product

def rotate(v,g):
    a,b,c=g
    return ((v & ~sum(1<<x for x in g)) | ((v>>a&1)<<b)
            | ((v>>b&1)<<c) | ((v>>c&1)<<a))

def compile_cnf(n,clauses):
    lanes=3*n
    start=finish=sum(1<<(3*i) for i in range(n))
    gates=[(3*i,3*i+1,3*i+2) for i in range(n)]
    for clause in clauses:
        w=lanes
        lanes+=3
        start|=1<<w
        finish|=1<<w
        gates += [(w,w+1,w+2)]*2
        for j,literal in enumerate(clause):
            false=3*(abs(literal)-1)+int(literal>0)
            t,f=lanes,lanes+1
            lanes+=2
            start|=1<<t
            finish|=1<<f
            gates.extend([(w+j,false,f),(false,t,f)])
        gates += [(w,w+2,w+1)]*2
    gates += [(3*i,3*i+2,3*i+1) for i in range(n)]
    return lanes,start,finish,gates

def decide(program):
    n,start,finish,gates=program
    last={i:j for j,g in enumerate(gates) for i in g}
    if any(i not in last and (start^finish)>>i&1 for i in range(n)):
        return False
    states={start}
    for j,g in enumerate(gates):
        states |= {rotate(v,g) for v in states}
        mask=sum(1<<i for i in g if last[i]==j)
        states={v for v in states if not (v^finish)&mask}
    return finish in states

def sat(n,clauses):
    return any(all(any(bits[abs(l)-1]==(l>0) for l in c) for c in clauses)
               for bits in product(range(2), repeat=n))

def check(n,clauses):
    network=compile_cnf(n,clauses)
    assert len(network[3])==2*n+10*len(clauses)
    assert network[0]==3*n+9*len(clauses)
    assert decide(network)==sat(n,clauses)

for x,y in product(range(2), repeat=2):
    states={x+2*y+4}
    for g in [(0,1,3),(1,2,3)]:
        states |= {rotate(v,g) for v in states}
    assert {v&3 for v in states if v>>2==2} == ({x+2*y} if not x*y else set())
clauses=list(product(*[(i,-i) for i in (1,2,3)]))
for mask in range(256):
    check(3,[c for i,c in enumerate(clauses) if mask>>i&1])
for cs in [[(1,1,1),(-1,-1,-1)],[(1,-1,1)],[(-1,-1,-1)]]:
    check(1,cs)
print('4 NAND inputs and 259 complete SAT/UNSAT compiler controls passed')
