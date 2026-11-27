from itertools import permutations,product
from random import Random
from recognizer import accepts,discover,recognize

def truth_cnf(n,values):
    return tuple(tuple(-(i+1) if x>>i&1 else i+1 for i in range(n))
                 for x in range(1<<n) if not values[x])

def ordered(n,truth,order):
    for k in range(n+1):
        prefix=order[:k]
        suffix=order[k:]
        def word(names,mask): return sum(((mask>>i)&1)<<j for i,j in enumerate(names))
        distinct={tuple(truth[word(prefix,x)|word(suffix,y)] for y in range(1<<len(suffix)))
                  for x in range(1<<k)}
        if len(distinct)>2: return False
    return True

def test_order(n,rows):
    truth=[accepts(rows,x) for x in range(1<<n)]
    expected=any(ordered(n,truth,o) for o in permutations(range(n)))
    status,program,_=recognize(n,rows,cap=200000,max_ternary=32)
    assert (status=="RECOGNIZED")==expected and status in ("RECOGNIZED","NO_ORDER")
    if program is not None:
        assert sorted(v for v,_ in program.layers)==list(range(1,n+1))
        assert list(map(program.evaluate,range(1<<n)))==truth
    return status

def tseitin(bad):
    edge=((1,2,3),(1,4,5),(2,4,6),(3,5,6))
    rows=[]
    for v,names in enumerate(edge):
        rhs=(bad and v==0)
        for vals in product((0,1),repeat=3):
            if sum(vals)%2!=rhs:
                rows.append(tuple(-i if a else i for i,a in zip(names,vals)))
    return rows

for f in range(256): test_order(3,truth_cnf(3,[(f>>x)&1 for x in range(8)]))
majority=((1,2),(2,3),(1,3))
assert test_order(3,majority)=="NO_ORDER"
assert test_order(3,truth_cnf(3,[x.bit_count()%2 for x in range(8)]))=="RECOGNIZED"
print("all 256 three-bit functions compared with all-order residual counts; 2CNF majority declined")
for bad in (False,True):
    rows=tseitin(bad)
    print("K4 native parity system",bad,test_order(6,rows),discover(6,rows,max_ternary=32)[:2])
    assert discover(6,rows,cap=2,max_ternary=32)[0]=="SKIP_BUDGET"
rng=Random(1701)
decisions=skips=0
for _ in range(400):
    n=rng.randrange(1,7)
    rows=[]
    for _ in range(rng.randrange(14)):
        names=rng.sample(range(1,n+1),rng.randrange(1,min(n,3)+1))
        rows.append(tuple(i if rng.getrandbits(1) else -i for i in names))
    expected=any(accepts(rows,x) for x in range(1<<n))
    status,w,_=discover(n,rows,candidates=[range(len(rows))])
    if status.startswith("SKIP"): skips+=1
    else:
        decisions+=1
        assert (status=="SAT")==expected
        if w is not None: assert accepts(rows,w)
assert discover(0,[()])[0]=="UNSAT"
assert discover(0,[])[0]=="SAT"
assert discover(2,[(1,-1),(2,2)],cap=0)[0]=="SKIP_BUDGET"
print("400 random original-CNF dispatches",decisions,"exact decisions",skips,"declines")
odd=truth_cnf(3,[x.bit_count()%2 for x in range(8)])
assert discover(3,odd+majority)[0:2]==("SAT",7)
assert discover(3,odd+majority+((-1,-2),))[0]=="UNSAT"
assert discover(2,((1,2),),candidates=[(0,)])[0]=="SAT"
print("shared parity factor plus unrecognized majority exterior: SAT witness 7, pinned-conflict variant UNSAT")
