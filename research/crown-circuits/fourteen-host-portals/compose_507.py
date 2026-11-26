from itertools import combinations
import json
from pathlib import Path
edges=list(combinations(range(4),2))+[(4+i,4+j) for j in range(5) for i in range(j) if (i,j) not in [(1,2),(3,4)]]
gates=[]
def gate(op,x,y):
    assert 0<=x<14+len(gates) and 0<=y<14+len(gates)
    gates.append((op,x,y))
    return 13+len(gates)
def either(x,y):return gate('OR',x,y)
def both(x,y):return gate('AND',x,y)
flags=[]
for vertex in range(9):
    first,*others=[i for i,e in enumerate(edges) if vertex in e]
    for i in others:first=either(first,i)
    flags.append(first)
assert len(gates)==19
a,b,c,d,t,i,j,k,l=flags
ab=either(a,b); cd=either(c,d)
small=either(both(both(a,b),cd),both(both(c,d),ab))
u=either(i,j);v=either(k,l)
large=either(either(both(i,j),both(k,l)),both(both(t,u),v))
cross=both(either(ab,cd),either(u,v))
out=either(either(small,large),cross)
full=(1<<16384)-1
sig=[]
for bit in range(14):
    half=1<<bit
    sig.append((full//((1<<(2*half))-1))*((1<<half)-1)*(1<<half))
for op,x,y in gates:sig.append(sig[x]&sig[y] if op=='AND' else sig[x]|sig[y])
assert sig[out]==full^(1+sum(1<<(1<<i) for i in range(14)))
assert len(gates)==39
print(len(gates),sum(op=='AND' for op,*_ in gates),'16384 OK')
Path(__file__).with_name('507-composed-39.json').write_text(json.dumps(dict(inputs=14,edges=edges,gates=gates,output=out),indent=2)+'\n')
