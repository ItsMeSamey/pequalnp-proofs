"""The exact 13-gate restriction and its threshold-five quotient in PG(2,3)."""
from itertools import product
q=3
def cross(x,y):
    v=tuple((x[(i+1)%3]*y[(i+2)%3]-x[(i+2)%3]*y[(i+1)%3])%q for i in range(3))
    s=next(t for t in v if t)
    return tuple(t*pow(s,-1,q)%q for t in v)
def inc(x,y):return sum(a*b for a,b in zip(x,y))%q==0
O=(0,0,1); pole=(0,1,1); pole2=(0,2,1); carrier=(1,0,0)
d=(0,1,0); row2=(1,2,0)
pts=[O,pole,(1,0,1),(2,0,1),(1,0,0)]
lines=[d]+[cross(pole,v) for v in pts[2:]]
assert all(inc(x,carrier) for x in (O,pole,pole2)) and inc(O,d) and inc(O,row2)
assert all(x in (pole,pole2) or any(inc(x,r) for r in (d,row2)) for x in pts)
assert all(y in (d,row2) or any(inc(x,y) for x in (pole,pole2)) for y in lines)
edges={(i,5+j) for i,x in enumerate(pts) for j,y in enumerate(lines) if inc(x,y)}
def truth(bits):return any(bits[i] and bits[j] for i,j in edges)
nodes=[]
def add(op,x,y):nodes.append((op,x,y));return 8+len(nodes)
block=add('&',5,add('|',add('|',add('|',0,2),3),4))
for i in range(3):
    block=add('|',block,add('&',6+i,add('|',1,2+i)))
def run(bits,repl=()):
    a=list(bits)
    for j,(op,x,y) in enumerate(nodes,9):
        a.append(a[repl[1]] if repl and j==repl[0] else a[x]&a[y] if op=='&' else a[x]|a[y])
    return a[block]
allrows=list(product((0,1),repeat=9))
assert all(run(b)==truth(b) for b in allrows)
assert all(any(run(b,(j,i))!=truth(b) for b in allrows) for j,(_,x,y) in enumerate(nodes,9) for i in (x,y))
for A,B,C,D,E in product((0,1),repeat=5):
    bits=(A,A,C,D,E,B,E,C,D)
    assert truth(bits)==(sum((A,B,C,D,E))>=2)
print(len(edges),'flags;',len(nodes),'gates; 512 full-cube tests, 26 bypass tests, 32 threshold tests passed')
